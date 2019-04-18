-- %default total

main : IO ()
main = 
     do theDir <- pure "/etc" --currentDir                                                                      
        Right dir <- dirOpen theDir | Left error => putStrLn ("dirOpen error: " ++ show error)
        showEntries dir
     where
        showEntries : Directory -> IO ()
        showEntries dir  = 
                    do Right nextEntry <- dirEntry dir | Left error => putStrLn ("dirEntry error: " ++ show error)
                       case the (Maybe String) nextEntry of
                         Just entry => do putStrLn (" entry: " ++ entry)
                                          showEntries dir
                         Nothing => pure ()
