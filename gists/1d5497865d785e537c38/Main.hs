instance Representable f => Distributive f where
    distribute = tabulate . distribute . fmap index
