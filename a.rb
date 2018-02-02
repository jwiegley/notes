hoursDiagram :: Budget UTCTime NominalDiffTime WorkDay
             -> QDiagram Cairo V2 Double Any
hoursDiagram budget
    = text textString # fontSizeL 0.5 # fc textColor
    <> (rect completionWidth barHeight # fc foregroundColor # alignR <>
       rect barWidth barHeight # fc barColor # alignR)
  where
    textString      = "100%"
    textColor       = white
    foregroundColor = red
    barColor        = blue
    barWidth        = 250
    barHeight       = 50
    completionWidth = 50
