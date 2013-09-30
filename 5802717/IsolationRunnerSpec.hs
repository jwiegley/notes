            fuzzCheck $ branch
                [ do pid <- start
                            True
                            [("main.hs", "main = print 5")]
                            []
                            Nothing

                     expect pid "5\n"
                , void $ start False
                      [("main.hs",
                        "import DoesNotExist\nmain = print 5")]
                      [] Nothing
                ]
