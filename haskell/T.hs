ap f g x = f x (g x)
proj x y = x
identity :: a -> a
identity = ap proj proj
