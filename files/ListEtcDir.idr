-- %default total

dirWasLastEntryOrError : Directory -> IO (Either FileError Bool)
dirWasLastEntryOrError (DHandle d)
    = do err <- foreign FFI_C "idris_dirError" (Ptr -> IO Int) d
         pure $ case err of
                  0 => Right False
                  -1 => Right True
                  _ => Left $ GenericFileError err

dirNextEntry : Directory -> IO (Either FileError (Maybe String))
dirNextEntry (DHandle d)
    = do fn <- foreign FFI_C "idris_nextDirEntry" (Ptr -> IO String) d
         Right wasLastEntry <- dirWasLastEntryOrError (DHandle d) | Left error => pure (Left error)
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
                    do Right nextEntry <- dirNextEntry dir | Left error => putStrLn ("dirEntry error: " ++ show error)
                       case nextEntry of
                         Just entry => do putStrLn (" entry: " ++ entry)
                                          showEntries dir
                         Nothing => pure ()
