-- File: Display
-- Description: This module contains some basic functions for printing
--              text

module Display(Display, displayString) where
 
-- This module defines polymorphic printing routines.
-- The polymorphism means that these routines can be used both by a
-- textual and a graphical user interface.
-- This polymorphism is realized by introducing a type-constructor
-- Display.

-- In a graphical UI, extra information is necessary to handle mouse-clicks
-- on parts of the text.
-- Therefore, Display contains a labelling function.
-- It also contains a 'basic' function for (unstructured) pieces of text,
-- and two concatenation functions for glueing stuff together
-- (horizontally or vertically)  


                
type Display label output =
      ([output]->output,           -- the horizontal concatenation function
       [output]->output,           -- the vertical concatenation function
       String->output,             -- the basic function
       label->output->output)      -- the labelling function

displayString :: Display label String
displayString = (concat, concat . (map (++"\n")), id, const id)

{-
-- for testing
displayString = 
         (concat,
          concat . (map (++"\n")),
          id,
          \label s -> show label ++ ":["++s++"]")
-}

{-
-- A much more elegant solution would be to introduce a CLASS Display.
-- Unfortunately, Haskells type system can't cope with an instance
-- Display String or Display [Char].

-- The class Display contains types that are used to display terms.
class Display label output where
      conc :: [output]->output          -- the concatenation function
      bas :: String->output             -- the basic function
      label :: label->output->output    -- the labelling function


instance Display a => Display [a] where
         conc = concat
         bas = id
         label _ s = s    -- we don't use the labels in the string 
                          -- representation
-}
