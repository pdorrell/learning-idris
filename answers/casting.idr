average : String -> Double
average phrase =
  let werds = words phrase
      numWords = length werds
      numChars = sum (map length werds)
      the_average = cast numChars / cast numWords in
   the_average


average2 : String -> Double
average2 phrase =
  let werds    = words phrase
      numWords = length werds
      swerds   = map length werds
      numChars = sum swerds
      result = cast numChars / cast numWords in
      result
