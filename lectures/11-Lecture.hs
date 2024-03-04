
-- Another data type of trees; this one is storing data in the nodes.
data Tree a = Leaf | Node (Tree a) a (Tree a)
  deriving (Show)

-- Here is an example tree.
intTree :: Tree Int
intTree = Node
            (Node Leaf 4 Leaf)
            5
            (Node
               (Node Leaf 7 Leaf)
               42
               Leaf)

-- By making Tree an instance of Functor, we give ourselves a method
-- for applying a function `f :: a -> b` to all the nodes in a tree,
-- giving us a function `fmap f :: Tree a -> Tree b`.

instance Functor Tree where
  fmap f Leaf = Leaf
  fmap f (Node l a r) = Node (fmap f l) (f a) (fmap f r)

-- For example, we can map a test for being odd over a tree full of
-- ints, resulting in a tree full of Booleans.

oddTree :: Tree Bool
oddTree = fmap (\ x -> x `mod` 2 == 1) intTree
