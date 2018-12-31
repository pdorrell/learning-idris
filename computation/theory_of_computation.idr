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
ProgrammingLanguage : (source_type, input_type, state_type, output_type : Type) -> Type
ProgrammingLanguage source_type input_type state_type output_type = source_type -> Program input_type state_type output_type

-- Execution status is either running or terminated
data ExecutionStatus = Running | Terminated | AlreadyTerminated

running_is_not_terminated : Running = Terminated -> Void
running_is_not_terminated Refl impossible

-- Execute one step of an executable program, taking into account whether or not it has already terminated
ExecuteStep : (program : Program _ state_type _) -> (ExecutionStatus, state_type) -> (ExecutionStatus, state_type)
ExecuteStep program (Running, state) = 
  case is_finished program state of
    True => (Terminated, state)
    False => (Running, update_state program state)
ExecuteStep program (Terminated, state) = (AlreadyTerminated, state)
ExecuteStep program (AlreadyTerminated, state) = (AlreadyTerminated, state)

-- Execute specified number of steps of program on initial state
ExecuteSteps : (program : Program input_type state_type _) -> (steps : Nat) -> (input : input_type) -> (ExecutionStatus, state_type)
ExecuteSteps program Z input = (Running, get_initial_state program input)
ExecuteSteps program (S k) input = ExecuteStep program (ExecuteSteps program k input) 

-- A program terminates executing from an initial state if after executing some number of steps it terminates
Terminates : (program : Program input_type state_type output_type) -> (input : input_type) -> (num_steps : Nat) -> 
                (result : output_type) -> Type
Terminates program input num_steps result = 
   (final_state : state_type ** (ExecuteSteps program num_steps input = (Terminated, final_state),
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
RunsForever program input = (num_steps : Nat) -> (state : state_type ** (ExecuteSteps program num_steps input = (Running, state)))

runs_forever_implies_not_terminates : RunsForever program input -> Terminates program input num_steps _ -> Void
runs_forever_implies_not_terminates {program} {input} {num_steps} runs_forever terminates = 
  let (final_state ** terminated_result) = terminates
      e1 = the (ExecuteSteps program num_steps input = (Terminated, final_state)) $ fst terminated_result
      e2 = runs_forever num_steps
      (running_state ** e3) = e2
      e4 = the (ExecuteSteps program num_steps input = (Running, running_state)) e3
      e5 = the ((Terminated, final_state) = (Running, running_state)) $ trans (sym e1) e4
      e6 = the (Terminated = Running) $ cong {f=fst} e5
  in running_is_not_terminated $ sym e6

x_implies_not_y_implies_y_implies_not_x : (x -> (y -> Void)) -> (y -> (x -> Void))
x_implies_not_y_implies_y_implies_not_x x_implies_not_y y1 x1 = x_implies_not_y x1 y1

terminates_implies_not_runs_forever : Terminates program input _ _ -> RunsForever program input -> Void
terminates_implies_not_runs_forever = x_implies_not_y_implies_y_implies_not_x runs_forever_implies_not_terminates

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

lemma_eq_max_steps : {input : input_type} -> {result : result_type} -> Terminates program input num_steps result -> 
                       Terminates (ProgramSteppedUntil program num_steps) input num_steps (Result result)

lemma_eq_max_steps {program} {input} {num_steps = Z} {result} terminates_program = 
  let (final_state ** (terminates_after_num_steps, gets_result)) = terminates_program
      cant_terminate_in_zero = the (Void) $ running_is_not_terminated $ cong {f=fst} terminates_after_num_steps
  in void cant_terminate_in_zero

lemma_eq_max_steps {program} {input} {num_steps = (S k)} {result} terminates_program = ?lemma_eq_max_steps_rhs_2
