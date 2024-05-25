{-# LANGUAGE Strict #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}
module ShortestPath where
import qualified Data.Set as S
import qualified Data.Map as M
import Utils ((|>), sndMap, minimumWith, fstMap)
import Data.Maybe (fromMaybe, isJust, mapMaybe, catMaybes, maybeToList, isNothing, fromJust)
import Control.Monad.Identity (Identity(runIdentity), foldM, forM, forM_)
import Control.Monad.Trans.Cont (evalCont, callCC)
import Control.Monad (when)
import Data.List (minimumBy, foldl')
import Control.Monad.Trans.Maybe (MaybeT(runMaybeT, MaybeT))
import Control.Monad.Cont (MonadTrans(lift))
import Test.QuickCheck (Arbitrary (arbitrary), Gen)
import qualified MyData.Vector as V
import Control.Monad.ST (runST)


type Graph v c = M.Map v (M.Map v c)

---------------------------------------- Dijkstra ----------------------------------------

dijkstraShortestPath :: (Ord k, Ord a, Num a) => Graph k a -> k -> k -> Maybe (a, [k])
dijkstraShortestPath graph src tar =
  loop M.empty (M.insert (0, src) [src] M.empty)
  |> fmap (sndMap reverse)
  where
    loop scanned pq = case M.minViewWithKey pq of
      Nothing -> Nothing
      Just (((dis, x), path), pq) -> evalCont $ callCC $ \ret -> do
        -- if scanned, just continue
        when (isJust $ scanned M.!? x) $ ret $ loop scanned pq
        -- add to scanned
        scanned <- return $ M.insert x (dis, path) scanned
        -- when the target is found, just return the current shortest distance and path
        when (x == tar) $ ret $ Just (dis, path)
        -- update priority queue
        pq <- return $ foldl (folder scanned dis path) pq $ M.toList $ getNext graph x
        return $ loop scanned pq
    folder scanned base path pq (v, dis)
      | isJust $ scanned M.!? v = pq
      | otherwise = M.insert (base + dis, v) (v:path) pq

getNext :: Ord k => Graph k v -> k -> M.Map k v
getNext graph v = fromMaybe M.empty $ graph M.!? v


------------------------------------- Bellmen-Ford -------------------------------------

bellmenFordShortestPath :: (Ord k, Ord a, Num a) => Graph k a -> k -> k -> Maybe (a, [k])
bellmenFordShortestPath graph src tar =
  let (vertices, revGraph) = genInfo graph in
  foldl (compute vertices revGraph) (M.insert src (0, [src]) M.empty) vertices
  |> M.lookup tar
  |> fmap (sndMap reverse)
  where
    -- generate the basic information
    genInfo graph =
      M.toList graph
      |> fmap (sndMap M.toList)
      |> foldl folder (S.empty, M.empty)
      |> fstMap S.toList
      where
        folder (vertices, map) (x, lst) =
          foldl' (folder' x) (S.insert x vertices, map) lst
        folder' v (vertices, map) (v', c) =
          (S.insert v' vertices, addToMap map v' v c)
        addToMap map v' v c = M.alter (addTo v c) v' map
        addTo v c maybeMap = Just $ M.insert v c $ fromMaybe M.empty maybeMap

    compute vertices revGraph cache _ =
      fmap findMinPath vertices
      |> catMaybes
      |> foldr (uncurry M.insert) cache
      -- maintain `src` to be the fixed value that should not be increased
      |> M.insert src (0, [src])
      where
        findMinPath v = case genPrevNodes v of
          []  -> Nothing
          lst -> Just (v, minimumWith fst lst)
        genPrevNodes v' = do
          -- get all the previous nodes
          (v, dis) <- M.toList $ fromMaybe M.empty $ revGraph M.!? v'
          -- for each node, get its found pointed value
          (base, path) <- maybeToList $ cache M.!? v
          return (base + dis, v':path)

maybeToTrans :: Monad m => Maybe a -> MaybeT m a
maybeToTrans = MaybeT . return

newtype ArbGraph k v = ArbGraph (Graph k v, k, k)
  deriving Show

instance (Arbitrary v, Num v) => Arbitrary (ArbGraph Int v) where
  arbitrary = do
    size <- (+1) <$> arbNat
    src <- arbInside size
    tar <- arbInside size

    lst <- forM [0..size-1] $ \idx -> do
      lst <- arbitrary
      let l = fmap (\(v, c) -> (mod v size, abs c)) lst
      return (idx, M.fromList l)

    return $ ArbGraph (M.fromList lst, src, tar)
    where
      arbNat :: Gen Int
      arbNat = abs <$> arbitrary
      arbInside size = (`mod` size) <$> arbNat

computeLen :: (Num a, Ord k) => Graph k a -> [k] -> Maybe a
computeLen _ [] = Just 0
computeLen _ [_] = Just 0
computeLen graph (v:lst@(v':_)) =
  case getNext graph v M.!? v' of
    Nothing -> Nothing
    Just l  -> do len <- computeLen graph lst; return $ len + l


-- prop> withMaxSuccess 10000 $ checkShortestPath
-- +++ OK, passed 10000 tests.
checkShortestPath :: ArbGraph Int Int -> Bool
checkShortestPath (ArbGraph (graph, src, tar)) =
  let res =
        [ dijkstraShortestPath graph src tar
        , bellmenFordShortestPath graph src tar
        ]
  in
  all lenCorrect res &&
  (all isNothing res ||
  (not (any isNothing res) &&
  allTheSame (fmap (fst . fromJust) res)))
  where
    lenCorrect Nothing = True
    lenCorrect (Just (len, path)) = case computeLen graph path of
      Nothing -> False
      Just l  -> l == len
    allTheSame [] = True
    allTheSame (x:lst) = all (==x) lst



------------------------------------ Floyd-Warshall ------------------------------------

data ExtNum x = ENUsual x | ENInf
  deriving (Eq, Ord, Show)

instance Num x => Num (ExtNum x) where
  (ENUsual x) + (ENUsual x') = ENUsual $ x + x'
  _ + _ = ENInf
  (*) = undefined
  abs (ENUsual x) = ENUsual $ abs x
  abs ENInf = ENInf
  signum (ENUsual x) = ENUsual $ signum x
  signum ENInf = ENInf
  fromInteger = ENUsual . fromIntegral
  negate = undefined

floydWarshallCore mat = do
  vLen <- V.len mat
  forM_ [0..vLen-1] $ \k ->
    forM_ [0..vLen-1] $ \i ->
      forM_ [0..vLen-1] $ \j -> do
        mij <- readMat mat i j
        mik <- readMat mat i k
        mkj <- readMat mat k j
        writeMat mat i j $ min mij (mik + mkj)

readMat mat i j = do
  ~(Just line) <- V.readAt mat i
  fromJust <$> V.readAt line j
writeMat mat i j v = do
  ~(Just line) <- V.readAt mat i
  V.writeAt line j v
  return ()

collectVertices :: Ord a => Graph a b -> [a]
collectVertices graph =
  M.toList graph
  |> fmap (\(v, map) -> v:fmap fst (M.toList map))
  |> concat
  |> S.fromList
  |> S.toList

graphToMat graph = do
  let vertices = collectVertices graph
  mat <- V.new
  forM_ vertices $ \_ -> do
    line <- V.new
    forM_ vertices $ \_ -> V.pushBack line ENInf
    V.pushBack mat line

  forM_ (M.toList graph) $ \(v, map) ->
    forM_ (M.toList map) $ \(v', c) ->
      writeMat mat v v' $ ENUsual c

  forM_ vertices $ \v ->
    writeMat mat v v $ ENUsual 0

  return mat

floydWarshallShortestPath graph src tar = runST $ do
  mat <- graphToMat graph
  floydWarshallCore mat
  n <- readMat mat src tar
  case n of
    ENUsual x -> return $ Just x
    ENInf -> return Nothing

-- prop> checkFloydWarshall
-- +++ OK, passed 100 tests.
checkFloydWarshall :: ArbGraph Int Int -> Bool
checkFloydWarshall (ArbGraph (graph, src, tar)) =
  floydWarshallShortestPath graph src tar ==
    (fst <$> dijkstraShortestPath graph src tar)

initMat n dflV = do
  mat <- V.new
  forM_ [0..n-1] $ \_ -> do
    line <- V.new
    forM_ [0..n-1] $ \_ -> V.pushBack line dflV
    V.pushBack mat line
  return mat

testMat :: [[Integer]]
testMat = runST $ do
  mat <- initMat 2 0
  writeMat mat 1 1 1
  writeMat mat 0 0 10
  lst <- V.toList mat
  forM lst V.toList
