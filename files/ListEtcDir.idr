-- %default total

myDirError : Directory -> IO Bool
myDirError (DHandle d)
    = do err <- foreign FFI_C "idris_dirError" (Ptr -> IO Int) d
         putStrLn ("err = " ++ (show err))
         pure (not (err == 0))

myDirEntry : Directory -> IO (Either FileError String)
myDirEntry (DHandle d)
    = do fn <- foreign FFI_C "idris_nextDirEntry" (Ptr -> IO String) d
         if !(myDirError (DHandle d))
            then pure (Left FileReadError)
            else pure (Right fn)

main : IO ()
main = 
     do theDir <- pure "/etc" --currentDir                                                                      
        Right dir <- dirOpen theDir | Left error => putStrLn ("dirOpen error: " ++ show error)
        showEntries dir
     where
        showEntries : Directory -> IO ()
        showEntries dir  = 
                    do Right entry <- myDirEntry dir | Left error => putStrLn ("dirEntry error: " ++ show error)
                       putStrLn (" entry: " ++ entry)
                       showEntries dir
