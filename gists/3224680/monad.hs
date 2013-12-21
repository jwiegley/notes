makeNode Empty Empty Empty = Empty
makeNode Empty Empty r = r
makeNode l Empty Empty = l

makeNode l Empty r = makeNode Empty l r

makeNode l (Leaf x) r = Node l x r

makeNode l (Node l' x r') r =
  Node (node' l l') x (node' r r')
  where
    node' Empty i = i
    node' i Empty = i
    node' l@(Leaf i) (Leaf j) = Node l j Empty
    node' l@(Node _ i _) (Leaf j) = Node l j Empty
    node' (Leaf i) r@(Node _ j _) = Node Empty i r
    node' l@(Node _ i _) r@(Node _ j _) = makeNode Empty l r
