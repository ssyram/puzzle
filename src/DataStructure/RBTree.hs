{-# LANGUAGE Strict #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}
module DataStructure.RBTree where
import Utils (eIMPOSSIBLE, (|>))
import Control.Monad (void, when)
import DataStructure.ClassSet (ISet (..), Check (..), testSet)
import Data.Maybe (fromMaybe)

data Color = Red | Black | DoubleBlack Bool deriving (Show, Eq)

data RBNode x
  = RBNode
    { key :: x
    , color :: Color
    , left :: RBNode x
    , right :: RBNode x }
  | RBLeaf deriving (Show)

newtype RBTree x = RBTree (RBNode x) deriving (Show)

isLeaf :: RBNode x -> Bool
isLeaf RBLeaf = True
isLeaf _ = False

-- Helper function to get the color of a node
getColor :: RBNode x -> Color
getColor RBLeaf = Black
getColor node = color node

-- Helper function to set the color of a node
setColor :: RBNode x -> Color -> RBNode x
setColor RBLeaf _ = RBLeaf
setColor node newColor = node { color = newColor }

rotateLeft :: RBNode x -> RBNode x
rotateLeft RBLeaf = error "Cannot rotate a leaf node"
rotateLeft (RBNode _ _ _ RBLeaf) = error "Right base node is empty when rotating left."
rotateLeft (RBNode c k l (RBNode rc rk rl rr)) = RBNode rc rk (RBNode c k l rl) rr

rotateRight :: RBNode x -> RBNode x
rotateRight RBLeaf = error "Cannot rotate a leaf node"
rotateRight (RBNode _ _ RBLeaf _) = error "Left base node is empty when rotating right."
rotateRight (RBNode c k (RBNode lc lk ll lr) r) = RBNode lc lk ll (RBNode c k lr r)

-- Convert tree to Dot format for visualization
toDot :: Show x => RBTree x -> String
toDot (RBTree node) = "digraph RBTree {\n" ++ toDot' "R" node ++ "}\n"

toDot' :: Show x => String -> RBNode x -> String
toDot' _ RBLeaf = ""
toDot' nodeId (RBNode key color left right) =
  let
    leftChildId = nodeId ++ "L"
    rightChildId = nodeId ++ "R"
    (nodeColor, fontColor, extraStyle) = case color of
      Red -> ("lightpink", "black", "")
      Black -> ("black", "white", "")
      DoubleBlack _ -> ("black", "white", ", peripheries=2")  -- DoubleBlack has double border
    thisNode = nodeId ++ " [label=\"" ++ show key ++ "\", style=filled, fillcolor=\"" ++ nodeColor ++ "\", fontcolor=\"" ++ fontColor ++ "\"" ++ extraStyle ++ "];\n"
    leftEdge = nodeId ++ " -> " ++ leftChildId ++ ";\n"
    rightEdge = nodeId ++ " -> " ++ rightChildId ++ ";\n"
    leftSubtree
      | isLeaf left = leftChildId ++ " [shape=point];\n"
      | otherwise   = toDot' leftChildId left
    rightSubtree
      | isLeaf right = rightChildId ++ " [shape=point];\n"
      | otherwise    = toDot' rightChildId right
  in
    thisNode ++ leftEdge ++ rightEdge ++ leftSubtree ++ rightSubtree


insert :: Ord x => RBTree x -> x -> RBTree x
insert (RBTree root) x = RBTree $ (insertNode root x) { color = Black }

insertNode :: Ord x => RBNode x -> x -> RBNode x
insertNode RBLeaf x = RBNode x Red RBLeaf RBLeaf
insertNode node@(RBNode k _ l r) x
  | k < x = adjust $ node { right = insertNode r x }
  | k > x = adjust $ node { left = insertNode l x }
  -- k == x, nothing to change
  | otherwise = node

adjust :: RBNode x -> RBNode x
adjust node@(RBNode k Black l@(RBNode _ Red _ _) r@(RBNode _ Red _ _))
  | hasRedChild l || hasRedChild r =
    RBNode k Red (l { color = Black }) (r { color = Black })
  | otherwise = node
-- from here on, the uncles should all be `Black`
-- LL pattern
adjust n@(RBNode _ Black (RBNode _ Red (RBNode _ Red _ _) _) _) =
  let ~n'@(RBNode _ _ _ r') = rotateRight n in
  n' { color = Black, right = r' { color = Red } }
-- LR 
adjust n@(RBNode _ Black l@(RBNode _ Red _ (RBNode _ Red _ _)) _) =
  let l' = rotateLeft l
      ~n'@(RBNode _ _ _ r') = rotateRight (n { left = l' })
  in n' { color = Black, right = r' { color = Red } }
-- RR pattern
adjust n@(RBNode _ Black _ (RBNode _ Red _ (RBNode _ Red _ _))) =
  let ~n'@(RBNode _ _ l' _) = rotateLeft n in
  n' { color = Black, left = l' { color = Red } }
-- RL
adjust n@(RBNode _ Black _ r@(RBNode _ Red (RBNode _ Red _ _) _)) =
  let r' = rotateRight r
      ~n'@(RBNode _ _ l' _) = rotateLeft (n { right = r' })
  in n' { color = Black, left = l' { color = Red } }
adjust node = node


hasRedChild :: RBNode x -> Bool
hasRedChild RBLeaf = False
hasRedChild (RBNode _ _ l r) = getColor l == Red || getColor r == Red


rbPropertyCheck :: RBTree x -> Either (String, [Char]) ()
rbPropertyCheck (RBTree node)
  | getColor node == Red = Left ("Root is not Black.", [])
  | otherwise = void $ checkRBNode node

checkRBNode :: (Num a, Eq a) => RBNode x -> Either (String, [Char]) a
checkRBNode RBLeaf = Right 1
checkRBNode node@(RBNode _ c l r)
  | c == Red && hasRedChild node = Left ("Consequent Red Nodes", [])
  | otherwise = do
    lc <- addToPath 'L' $ checkRBNode l
    rc <- addToPath 'R' $ checkRBNode r
    when (lc /= rc) $ Left ("Black Count not the same.", [])
    case c of
      Red   -> return lc
      Black -> return $ lc + 1
      DoubleBlack _ -> Left ("Has Double Black Color.", [])
  where
    addToPath c (Left (err, path)) = Left (err, c:path)
    addToPath _ right = right


rbMsgCheck :: RBTree x -> Bool
rbMsgCheck tree = case rbPropertyCheck tree of
  Left (err, path) -> concat
    [ "Error Found: "
    , err
    , "; at path: \""
    , path
    , "\"." ]
    |> error
  Right () -> True


empty :: RBTree x
empty = RBTree RBLeaf

printAdd :: IO ()
printAdd =
  [0,1,-1,-2,-3,-4]
  |> foldl insert empty
  |> toDot
  |> putStrLn

-- prop> withMaxSuccess 100000 testAdd
-- +++ OK, passed 100000 tests.
testAdd :: [Int] -> Bool
testAdd l =
  l
  |> foldl insert empty
  |> rbMsgCheck



remove :: Ord x => RBTree x -> x -> RBTree x
remove (RBTree node) x = RBTree $ case removeNode node x of
  RBLeaf -> RBLeaf
  RBNode _ (DoubleBlack True) _ _ -> RBLeaf
  node -> node { color = Black }


removeNode :: Ord x => RBNode x -> x -> RBNode x
removeNode RBLeaf _ = RBLeaf
removeNode node@(RBNode k c l r) x
  | k < x = rmAdjust $ node { right = removeNode r x }
  | k > x = rmAdjust $ node { left = removeNode l x }
  -- k == x
  | isLeaf l && isLeaf r = case c of
    Red -> RBLeaf  -- just delete
    Black -> node { color = DoubleBlack True }
    DoubleBlack _ -> error "UNKNOWN DOUBLE BLACK WHEN DELETING."
  | isLeaf l = r { color = Black }
  | isLeaf r = l { color = Black }
  | otherwise =
    let (newVal, r') = removeLeftMost r in
    rmAdjust $ node { key = newVal, right = r' }

removeLeftMost :: RBNode x -> (x, RBNode x)
removeLeftMost RBLeaf = eIMPOSSIBLE
removeLeftMost node@(RBNode k c l r)
  | isLeaf l =
    if not $ isLeaf r then (k, r { color = Black })
    else if c == Red then (k, RBLeaf)
    else (k, node { color = DoubleBlack True })
  | otherwise =
    let (newVal, l') = removeLeftMost l in
    (newVal, rmAdjust $ node { left = l' })

-- rmAdjust 
-- DoubleBlack with brother being Red
rmAdjust :: RBNode x -> RBNode x
rmAdjust n@(RBNode _ _ (RBNode _ (DoubleBlack _) _ _) r@(RBNode _ Red _ _)) =
  let ~n'@(RBNode _ _ l' _) = rotateLeft $ n { color = Red, right = r { color = Black }}
  in n' { left = rmAdjust l' }
rmAdjust n@(RBNode _ _ l@(RBNode _ Red _ _) (RBNode _ (DoubleBlack _) _ _)) =
  let ~n'@(RBNode _ _ _ r') = rotateRight $ n { color = Red, left = l { color = Black }}
  in n' { right = rmAdjust r' }
-- DoubleBlack with brother that could only be Black
-- RR
rmAdjust n@(RBNode _ c l@(RBNode _ (DoubleBlack b) _ _)
            r@(RBNode _ cr _ rr@(RBNode _ Red _ _)))
  = let rr' = rr { color = cr }
        r'  = r  { color = c, right = rr' }
        l'  = if b then RBLeaf else l { color = Black }
        n'  = n { color = Black, left = l', right = r' }
    in rotateLeft n'
-- LL
rmAdjust n@(RBNode _ c l@(RBNode _ cl ll@(RBNode _ Red _ _) _)
            r@(RBNode _ (DoubleBlack b) _ _))
  = let ll' = ll { color = cl }
        l'  = l  { color = c, left = ll' }  -- l' will be the new top, it keeps the original color `c`
        r'  = if b then RBLeaf else r { color = Black }
        n'  = n { color = Black, left = l', right = r' }
    in rotateRight n'
-- RL
rmAdjust n@(RBNode _ c l@(RBNode _ (DoubleBlack b) _ _)
            r@(RBNode _ _ rl@(RBNode _ Red _ _) _))
  = let rl' = rl { color = c }  -- rl' will be the new top, this top keeps the original color `c`
        r'  = rotateRight $ r  { left = rl' }
        l'  = if b then RBLeaf else l { color = Black }
        n'  = n { color = Black, left = l', right = r' }
    in rotateLeft n'
-- LR
rmAdjust n@(RBNode _ c l@(RBNode _ _ _ lr@(RBNode _ Red _ _))
            r@(RBNode _ (DoubleBlack b) _ _))
  = let lr' = lr { color = c }
        l'  = rotateLeft $ l  { right = lr' }
        r'  = if b then RBLeaf else r { color = Black }
        n'  = n { color = Black, left = l', right = r' }
    in rotateRight n'
-- All Black in the children of brother `r`
rmAdjust n@(RBNode _ c l@(RBNode _ (DoubleBlack b) _ _) r) =
    let r' = r { color = Red }
        l' = if b then RBLeaf else l { color = Black }
        n' = n { left = l', right = r' }
    in case c of
      Red -> n' { color = Black }
      -- do not delete this node when the double black is erased
      Black -> n' { color = DoubleBlack False }
      DoubleBlack _ -> error "When moving double black upward, encountered another double black."
-- All Black in the children of brother `l`
rmAdjust n@(RBNode _ c l r@(RBNode _ (DoubleBlack b) _ _)) =
    let l' = l { color = Red }
        r' = if b then RBLeaf else r { color = Black }
        n' = n { left = l', right = r' }
    in case c of
      Red -> n' { color = Black }
      -- do not delete this node when the double black is erased
      Black -> n' { color = DoubleBlack False }
      DoubleBlack _ -> error "When moving double black upward, encountered another double black."
rmAdjust node = node

inNode :: Ord a => RBNode a -> a -> Bool
inNode RBLeaf _ = False
inNode (RBNode k _ l r) x
  | k < x     = inNode r x
  | k > x     = inNode l x
  | otherwise = True

sizeNode :: Num p => RBNode x -> p
sizeNode RBLeaf = 0
sizeNode (RBNode _ _ l r) = 1 + sizeNode l + sizeNode r

instance Ord x => ISet (RBTree x) where
  type Element (RBTree x) = x
  emptySet :: Ord x => RBTree x
  emptySet = empty
  addToSet :: Ord x => RBTree x -> Element (RBTree x) -> RBTree x
  addToSet = insert
  inSet :: Ord x => RBTree x -> Element (RBTree x) -> Bool
  inSet (RBTree rn) x = inNode rn x
  removeFromSet :: Ord x => RBTree x -> Element (RBTree x) -> RBTree x
  removeFromSet = remove
  sizeSet :: (Ord x, Integral i) => RBTree x -> i
  sizeSet (RBTree rn) = sizeNode rn

instance Check (RBTree x) where
  check :: RBTree x -> RBTree x
  check tree
    | rbMsgCheck tree = tree
    | otherwise = undefined

-- prop> withMaxSuccess 10000000 $ testRBTree
-- +++ OK, passed 10000000 tests.
testRBTree :: [(Int, Int)] -> Bool
testRBTree = testSet empty

-- | Find the largest element that is smaller or equal to the given number
--
-- >>> maxLe (fromList [1, 2, 3, 5, 6, 7]) 4
-- Just 3
maxLe :: Ord a => RBTree a -> a -> Maybe a
maxLe (RBTree node) = maxLeNode node

fromList :: (Foldable t, Ord x) => t x -> RBTree x
fromList = foldl insert empty

-- | Find the largest element that is smaller or equal to the given number
maxLeNode :: Ord a => RBNode a -> a -> Maybe a
maxLeNode RBLeaf _ = Nothing
maxLeNode (RBNode k _ l r) v
  | k == v = Just k
  | k < v  = Just $ fromMaybe k $ maxLeNode r v
  -- v < k
  | otherwise = maxLeNode l v

-- | Find the smallest element that is larger than or equal to the given number
-- 
-- >>> minGe (fromList [1, 2, 3, 5, 6, 7]) 4
-- Just 5
minGe :: Ord a => RBTree a -> a -> Maybe a
minGe (RBTree node) = minGeNode node

-- | Find the smallest element that is larger than or equal to the given number
minGeNode :: Ord a => RBNode a -> a -> Maybe a
minGeNode RBLeaf _ = Nothing
minGeNode (RBNode k _ l r) v
  | k == v = Just k
  | k < v  = minGeNode r v
  -- v < k
  | otherwise = Just $ fromMaybe k $ minGeNode l v
