%default total

-- exploring the idea that a meaningful set of mathematical axioms
-- defines a theory of computation.

-- A program starts by converting the input value to initial execution state,
-- then executes one step at a time by updating the current execution state,
-- reporting if it has finished yet. And the final state can then be converted
-- into the output value.
record Program input_type state_type output_type where
  constructor MkProgram
  get_initial_state : input_type -> state_type
  is_finished : state_type -> Bool
  update_state : state_type -> state_type
  get_result : state_type -> output_type

-- A programming language maps source code to an executable program
-- (So it's really a programming language _and_ a compiler/interpreter.)
ProgrammingLanguage : (source_type, input_type, state_type, output_type : Type) -> Type
ProgrammingLanguage source_type input_type state_type output_type = source_type -> Program input_type state_type output_type

-- This type represents the computation executing num_steps steps
data StateUpdateTerminatesOrNot : (program : Program input_type state_type output_type) -> (state : state_type) -> (num_steps : Nat) -> 
                                  (terminates : Bool) -> (final_state : state_type) -> Type where
 InitialStateFinished : (is_finished program state = terminates) -> 
                          StateUpdateTerminatesOrNot program state Z terminates state
 NextStateTerminates : (is_finished program state = False) -> 
                          StateUpdateTerminatesOrNot program (update_state program state) k terminates final_state ->
                          StateUpdateTerminatesOrNot program state (S k) terminates final_state
                          
StateUpdateTerminates : (program : Program input_type state_type output_type) -> (state : state_type) -> (num_steps : Nat) -> 
                          (final_state : state_type) -> Type
StateUpdateTerminates program state num_steps = StateUpdateTerminatesOrNot program state num_steps True
                          
not__terminates_and_not_terminates : StateUpdateTerminates program state num_steps _ -> 
                                       StateUpdateTerminatesOrNot program state num_steps False _ -> Void
not__terminates_and_not_terminates {num_steps = Z} (InitialStateFinished finished1) (InitialStateFinished finished2) = 
   trueNotFalse $ trans (sym finished1) finished2
not__terminates_and_not_terminates {num_steps = (S k)}
   (NextStateTerminates finished1 terminates_k) (NextStateTerminates finished2 not_terminates_k) = 
       not__terminates_and_not_terminates terminates_k not_terminates_k

StateUpdateRunsForever : (program : Program input_type state_type output_type) -> (state : state_type) -> Type
StateUpdateRunsForever program state = 
   (num_steps : Nat) -> (final_state : state_type ** (StateUpdateTerminatesOrNot program state num_steps False final_state))
   
not_state_update_terminates_and_runs_forever : StateUpdateTerminates program state num_steps final_state -> 
                                                  StateUpdateRunsForever program state -> Void
                          
not_state_update_terminates_and_runs_forever {program} {state} {num_steps} {final_state} terminates runs_forever = 
  let (final_state ** not_terminates) = runs_forever num_steps
  in not__terminates_and_not_terminates terminates not_terminates

Terminates : (program : Program input_type state_type output_type) -> (input : input_type) -> (num_steps : Nat) -> 
                (result : output_type) -> Type
Terminates program input num_steps result = 
   (final_state : state_type ** (StateUpdateTerminates program (get_initial_state program input) num_steps final_state,
                                 get_result program final_state = result))

-- If termination of program1 implies termination of program2, then we can use program1 wherever we want to use program2
-- (if the only thing we are interested in is the result of program2 terminating).
ImpliesTermination : (program1 : Program input_type _ output_type) -> 
                        (program2 : Program input_type _ output_type) -> Type
ImpliesTermination {input_type} {output_type} program1 program2 = 
   {input: input_type} -> {result : output_type} ->
      (num_steps1: Nat ** Terminates program1 input num_steps1 result) ->
      (num_steps2: Nat ** Terminates program2 input num_steps2 result)

-- 'Runs Forever' means that after any number of steps, the program is still running
RunsForever : (program : Program input_type state_type _) -> (input : input_type) -> Type
RunsForever program input = StateUpdateRunsForever program (get_initial_state program input)

runs_forever_implies_not_terminates : RunsForever program input -> Terminates program input num_steps _ -> Void
runs_forever_implies_not_terminates {program} {input} {num_steps} runs_forever terminates = 
    let (final_state ** (state_update_terminates, _)) = terminates
in not_state_update_terminates_and_runs_forever state_update_terminates runs_forever

x_implies_not_y_implies_y_implies_not_x : (x -> (y -> Void)) -> (y -> (x -> Void))
x_implies_not_y_implies_y_implies_not_x x_implies_not_y y1 x1 = x_implies_not_y x1 y1

data ResultSoFar t = NoResultYet | Result t

data CountingDown t = StillCountingDown Nat t | CountDownFinished

ProgramSteppedUntil : Program input_type state_type output_type -> (max_steps : Nat) -> 
                         Program input_type (CountingDown state_type) (ResultSoFar output_type)
ProgramSteppedUntil program max_steps = 
  MkProgram stepped_get_initial_state stepped_is_finished stepped_update_state stepped_get_result
    where
      stepped_get_initial_state : input_type -> CountingDown state_type
      stepped_get_initial_state input = StillCountingDown max_steps $ get_initial_state program input
      
      stepped_is_finished : CountingDown state_type -> Bool
      stepped_is_finished CountDownFinished = True
      stepped_is_finished (StillCountingDown Z state) = True
      stepped_is_finished (StillCountingDown (S k) state) = is_finished program state
      
      stepped_update_state : CountingDown state_type -> CountingDown state_type
      stepped_update_state CountDownFinished = CountDownFinished
      stepped_update_state (StillCountingDown Z state) = CountDownFinished
      stepped_update_state (StillCountingDown (S k) state) = StillCountingDown k $ update_state program state
      
      stepped_get_result : CountingDown state_type -> ResultSoFar output_type
      stepped_get_result CountDownFinished = NoResultYet
      stepped_get_result (StillCountingDown _ state) = Result $ get_result program state
      
data NotPastMax : Nat -> Nat -> Type where
  ZeroNotPastAnyMax : Nat -> NotPastMax Z n
  SuccNotPastMax : NotPastMax x y -> NotPastMax (S x) (S y)
