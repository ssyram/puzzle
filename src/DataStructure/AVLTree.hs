{-# LANGUAGE Strict #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}
module DataStructure.AVLTree where
import Data.Maybe (fromJust, isNothing, isJust)
import Utils ((|>), eIMPOSSIBLE)
import qualified Data.Set as S
import DataStructure.ClassSet (ISet (..))

data AVLNode x
  = AVLNode
    { key :: x
    , height :: Int
    , left :: AVLNode x
    , right :: AVLNode x }
  | AVLLeaf deriving (Show)


isLeaf :: AVLNode x -> Bool
isLeaf AVLLeaf = True
isLeaf _othws = False

newtype AVLTree x = AVLTree (AVLNode x)

getHeight :: AVLNode x -> Int
getHeight AVLLeaf = 0
getHeight node = height node

getBalance :: AVLNode x -> Int
getBalance AVLLeaf = 0
getBalance node = getHeight (right node) - getHeight (left node)

replaceChildNode :: AVLNode x -> Either (AVLNode x) (AVLNode x) -> AVLNode x
replaceChildNode node newChild =
  case node of
    AVLLeaf -> error "Cannot add a new left node to a leaf node."
    node    ->
      case newChild of
        Left  newLeft  ->
          let newHeight = 1 + max (getHeight $ right node) (getHeight newLeft) in
          node { height = newHeight, left = newLeft }
        Right newRight ->
          let newHeight = 1 + max (getHeight $ left node) (getHeight newRight) in
          node { height = newHeight, right = newRight }

rotateLeft :: AVLNode x -> AVLNode x
rotateLeft AVLLeaf = error "Cannot rotate a leaf node"
rotateLeft node =
  case right node of
    AVLLeaf -> error "Right base node is empty when rotating left."
    rightNode ->
      replaceChildNode node (Right $ left rightNode)
      |> replaceChildNode rightNode . Left

rotateRight :: AVLNode x -> AVLNode x
rotateRight AVLLeaf = error "Cannot rotate a leaf node"
rotateRight node =
  case left node of
    AVLLeaf -> error "Left base node is empty when rotating right."
    leftNode ->
      replaceChildNode node (Left $ right leftNode)
      |> replaceChildNode leftNode . Right

makeBalance :: AVLNode x -> AVLNode x
makeBalance AVLLeaf = AVLLeaf
makeBalance node
  | balance <= 1 && balance >= -1 = node
  -- RR, rightBalance == 0 | 1
  | balance == 2 && rightBalance >= 0 = rotateLeft node
  -- RL
  | balance == 2 && rightBalance == -1 =
    let newRight = rotateRight $ right node in
    rotateLeft $ replaceChildNode node $ Right newRight
  -- LR
  | balance == -2 && leftBalance == 1 =
    let newLeft = rotateLeft $ left node in
    rotateRight $ replaceChildNode node $ Left newLeft
  -- LL, leftBalance == 0 | -1
  | balance == -2 && leftBalance <= 0 = rotateRight node
  | otherwise =
    error $ concat
      [ "Error: Balance number: "
      , show balance
      , "; left balance: "
      , show leftBalance
      , "; right balance:"
      , show rightBalance ]
  where
    balance = getBalance node
    leftBalance = getBalance $ left node
    rightBalance = getBalance $ right node

addToNode :: Ord x => AVLNode x -> x -> AVLNode x
addToNode AVLLeaf x = AVLNode x 1 AVLLeaf AVLLeaf
addToNode node x
  | key node == x = node
  | key node < x  = modifyRightChild (`addToNode` x) node
  | otherwise     = modifyLeftChild (`addToNode` x) node

modifyRightChild :: (AVLNode x -> AVLNode x) -> AVLNode x -> AVLNode x
modifyRightChild f node =
  f (right node)
  |> replaceChildNode node . Right
  |> makeBalance

modifyLeftChild :: (AVLNode x -> AVLNode x) -> AVLNode x -> AVLNode x
modifyLeftChild f node =
  f (left node)
  |> replaceChildNode node . Left
  |> makeBalance

deleteFromNode :: Ord x => AVLNode x -> x -> AVLNode x
deleteFromNode AVLLeaf _ = AVLLeaf
deleteFromNode node x
  | key node < x = modifyRightChild (`deleteFromNode` x) node
  | key node > x = modifyLeftChild (`deleteFromNode` x) node
  -- key node == x
  | isLeaf (left node) && isLeaf (right node) = AVLLeaf
  -- the node must be with two leaves
  -- otherwise it violates the AVL construction that
  -- left is at least 2 heigher than right
  | isLeaf $ right node = left node
  | otherwise =
    let (newVal, newNode) = delLeftMost $ right node in
    makeBalance $ replaceChildNode (node { key = newVal }) $ Right newNode
  where
    delLeftMost AVLLeaf = error "Searching left-most node from a leaf."
    delLeftMost node
      | isLeaf $ left node = (key node, right node)
      | otherwise =
        let (newVal, newNode) = delLeftMost $ left node in
        (newVal, makeBalance $ replaceChildNode node $ Left newNode)

inNode :: Ord x => AVLNode x -> x -> Bool
inNode AVLLeaf _ = False
inNode node x
  | key node < x = inNode (right node) x
  | key node > x = inNode (left node) x
  | otherwise = True

emptyTree :: AVLTree x
emptyTree = AVLTree AVLLeaf

test :: IO ()
test = putStrLn $ toDot $ AVLTree node
  where
    node =
      fmap snd [(0,1),(0,2),(0,-6),(0,-7),(0,0),(0,-8),(0,4),(0,5),(0,-9),(0,6),(0,3)]
      |> foldl addToNode AVLLeaf
      |> flip deleteFromNode (-6)

lstOperation :: (Integral a, Ord x, Show x) => [(a, x)] -> [Bool]
lstOperation lst = fst $ foldl folder ([], AVLLeaf) lst
  where
    folder (acc, node) (opCode, el)
      | not (heightCorrect node && isBalance node) =
        error $ "Height buff not correct or is not balance. Tree:\n" ++ toDot (AVLTree node)
      | otherwise =
        case abs $ opCode `mod` 3 of
          -- add
          0 -> (acc, addToNode node el)
          -- delete
          1 -> (acc, deleteFromNode node el)
          -- search
          2 -> (inNode node el:acc, node)
          _ -> eIMPOSSIBLE ()

trueLstOperation :: (Integral a1, Ord a2) => [(a1, a2)] -> [Bool]
trueLstOperation lst = fst $ foldl folder ([], S.empty) lst
  where
    folder (acc, set) (opCode, el) =
      case abs $ opCode `mod` 3 of
        -- add
        0 -> (acc, S.insert el set)
        -- delete
        1 -> (acc, S.delete el set)
        -- search
        2 -> (S.member el set:acc, set)
        _ -> eIMPOSSIBLE ()

heightCorrect :: AVLNode x -> Bool
heightCorrect node = snd $ hCorrect node
  where hCorrect AVLLeaf = (0, True)
        hCorrect (AVLNode _ h left right) =
          let (lH, lB) = hCorrect left
              (rH, rB) = hCorrect right
          in (h, lB && rB && h == 1 + max lH rH)

isBalance :: AVLNode x -> Bool
isBalance AVLLeaf = True
isBalance node
  | balance > 1 || balance < -1 = False
  | otherwise = isBalance (left node) && isBalance (right node)
  where balance = getBalance node

-- prop> withMaxSuccess 10000000 testAVLTree
-- +++ OK, passed 10000000 tests.
testAVLTree :: [(Int, Int)] -> Bool
testAVLTree l = lstOperation l == trueLstOperation l


toDot :: Show x => AVLTree x -> String
toDot (AVLTree node) = "digraph AVLTree {\n" ++ toDot' "R" node ++ "}\n"

toDot' :: Show x => String -> AVLNode x -> String
toDot' _ AVLLeaf = ""
toDot' nodeId (AVLNode key height left right) =
  let
    leftChildId = nodeId ++ "L"
    rightChildId = nodeId ++ "R"
    thisNode = nodeId ++ " [label=\"" ++ show key ++ " (h=" ++ show height ++ ")\"];\n"
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

sizeNode :: Num p => AVLNode x -> p
sizeNode AVLLeaf = 0
sizeNode (AVLNode _ _ l r) = 1 + sizeNode l + sizeNode r

instance Ord x => ISet (AVLTree x) where
  type Element (AVLTree x) = x
  emptySet :: Ord x => AVLTree x
  emptySet = AVLTree AVLLeaf
  addToSet :: Ord x => AVLTree x -> Element (AVLTree x) -> AVLTree x
  addToSet = addToAVLTree
  inSet :: Ord x => AVLTree x -> Element (AVLTree x) -> Bool
  inSet (AVLTree an) x = inNode an x
  removeFromSet :: Ord x => AVLTree x -> Element (AVLTree x) -> AVLTree x
  removeFromSet (AVLTree an) x = AVLTree $ deleteFromNode an x
  sizeSet :: (Ord x, Integral i) => AVLTree x -> i
  sizeSet (AVLTree an) = sizeNode an

-- addToNode Nothing x = (True, AVLNode x 1 Nothing Nothing)
-- addToNode (Just node) x
--   | key node == x = (False, node)
--   | key node < x = tryAddRight node x
--   | otherwise = tryAddLeft node x
--   where
--     tryAddRight node x =
--       case addToNode (right node) x of
--         (False, _) -> (False, node)
--         (True, cn) ->
--           let newBalance = balance node + 1 in
--           if newBalance <= 1 then (True, node { balance = newBalance, right = Just cn })
--           -- otherwise `newBalance` is `2`
--           -- then see which way to go, RR
--           else if balance cn == 1 then (True, turnRight node)
--           -- else, RL
--           else (True, turnRight node (turnLeft cn))

addToAVLTree :: Ord x => AVLTree x -> x -> AVLTree x
addToAVLTree (AVLTree node) = AVLTree . addToNode node
