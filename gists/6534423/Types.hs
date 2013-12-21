cancelTaskForId :: TaskId s -> EventQueue s -> EventQueue s
cancelTaskForId tid xs = xs & _Middle %~ f
    where
      f Nothing = Nothing
      f (Just ev)
          | taskId ev == tid = Nothing
          | otherwise = Just ev
