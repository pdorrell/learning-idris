%default total

-- exploring the idea that a meaningful set of mathematical axioms
-- defines a theory of computation.

-- A program starts by converting the input value to initial execution state,
-- then executes one step at a time by updating the current execution state,
-- reporting if it has finished yet. And the final state can then be converted
-- into the output value.
record Program input_type state_type output_type where
  constructor MkProgram
  get_initial_state: input_type -> state_type
  execute_step : state_type -> (Bool, state_type)
  get_result : state_type -> output_type

-- A programming language maps source code to an executable program
ProgrammingLanguage : (source_type, input_type, state_type, output_type : Type) -> Type
ProgrammingLanguage source_type input_type state_type output_type = source_type -> Program input_type state_type output_type

-- Execution state is either running with current state, or terminated with current (and final) state
data ExecutionState state_type = Running state_type | Terminated state_type

running_is_not_terminated : Running running_state = Terminated terminated_state -> Void
running_is_not_terminated Refl impossible

-- Execute one step of an executable program, taking into account whether or not it has already terminated
ExecuteStep : (program : Program _ state_type _) -> ExecutionState state_type -> ExecutionState state_type
ExecuteStep program (Running state) = 
  let (terminated, updated_state) = execute_step program state
  in case terminated of
       True => Terminated updated_state
       False => Running updated_state
ExecuteStep program (Terminated state) = Terminated state

-- Execute specified number of steps of program on initial state
ExecuteSteps : (program : Program input_type state_type _) -> (steps : Nat) -> (input : input_type) -> ExecutionState state_type
ExecuteSteps program Z input = Running $ get_initial_state program input
ExecuteSteps program (S k) input = ExecuteStep program (ExecuteSteps program k input) 

-- A program terminates executing from an initial state if after executing some number of steps it terminates
Terminates : (program : Program input_type state_type output_type) -> (input : input_type) -> (result : output_type) -> Type
Terminates program input result = (num_steps: Nat ** 
                                      (final_state : state_type ** 
                                        (ExecuteSteps program num_steps input = Terminated final_state,
                                         get_result program final_state = result)))

-- If termination of program1 implies termination of program2, then we can use program1 wherever we want to use program2
-- (if the only thing we are interested in is the result of program2 terminating).
ImpliesTermination : (program1 : Program input_type _ output_type) -> 
                      (program2 : Program input_type _ output_type) -> Type
ImpliesTermination {input_type} {output_type} program1 program2 = 
   {input: input_type} -> {result : output_type} 
     -> Terminates program1 input result
     -> Terminates program2 input result

-- 'Runs Forever' means that after any number of steps, the program is still running
RunsForever : (program : Program input_type state_type _) -> (input : input_type) -> Type
RunsForever program input = (num_steps : Nat) -> (state : state_type ** ExecuteSteps program num_steps input = Running state)

runs_forever_implies_not_terminates : RunsForever program input -> Terminates program input _ -> Void
runs_forever_implies_not_terminates {program} {input} runs_forever terminates = 
  let (num_steps ** (final_state ** terminated_result)) = terminates
      e1 = the (ExecuteSteps program num_steps input = Terminated final_state) $ fst terminated_result
      e2 = runs_forever num_steps
      (running_state ** e3) = e2
      e4 = the (ExecuteSteps program num_steps input = Running running_state) e3
      e5 = the (Terminated final_state = Running running_state) $ trans (sym e1) e4
  in running_is_not_terminated $ sym e5

x_implies_not_y_implies_y_implies_not_x : (x -> (y -> Void)) -> (y -> (x -> Void))
x_implies_not_y_implies_y_implies_not_x x_implies_not_y y1 x1 = x_implies_not_y x1 y1

terminates_implies_not_runs_forever : Terminates program initial_state result -> RunsForever program initial_state -> Void
terminates_implies_not_runs_forever = x_implies_not_y_implies_y_implies_not_x runs_forever_implies_not_terminates
