-- %default total

dirNoMoreEntries : Directory -> IO (Either FileError Bool)
dirNoMoreEntries (DHandle d)
    = do err <- foreign FFI_C "idris_dirError" (Ptr -> IO Int) d
         pure $ case err of
                  0 => Right False
                  -1 => Right True
                  _ => Left $ GenericFileError err

dirEntry : Directory -> IO (Either FileError (Maybe String))
dirEntry (DHandle d)
    = do fn <- foreign FFI_C "idris_nextDirEntry" (Ptr -> IO String) d
         Right wasLastEntry <- dirNoMoreEntries (DHandle d) | Left error => pure (Left error)
         pure $ Right $ case wasLastEntry of
                          False => Just fn
                          True => Nothing

main : IO ()
main = 
     do theDir <- pure "/etc" --currentDir                                                                      
        Right dir <- dirOpen theDir | Left error => putStrLn ("dirOpen error: " ++ show error)
        showEntries dir
     where
        showEntries : Directory -> IO ()
        showEntries dir  = 
                    do Right nextEntry <- Main.dirEntry dir | Left error => putStrLn ("dirEntry error: " ++ show error)
                       case nextEntry of
                         Just entry => do putStrLn (" entry: " ++ entry)
                                          showEntries dir
                         Nothing => pure ()
