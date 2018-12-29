%default total


-- exploring the idea that a meaningful set of mathematical axioms
-- defines a theory of computation.

-- A program executes one step by updating the current execution state,
-- and reporting if it has finished.
ProgramType : (state_type : Type) -> Type
ProgramType state_type = state_type -> (Bool, state_type)

-- A programming language maps source code to an executable program
ProgrammingLanguage : (source_type, state_type : Type) -> Type
ProgrammingLanguage source_type state_type = source_type -> ProgramType state_type

-- Execution state is either running with current state, or terminated with current (and final) state
data ExecutionState state_type = Running state_type | Terminated state_type

running_is_not_terminated : Running running_state = Terminated terminated_state -> Void
running_is_not_terminated Refl impossible

has_terminated : ExecutionState state_type -> Bool
has_terminated (Running x) = False
has_terminated (Terminated x) = True

-- Execute one step of an executable program, taking into account whether or not it has already terminated
ExecuteStep : (program : ProgramType state_type) -> ExecutionState state_type -> ExecutionState state_type
ExecuteStep program (Running state) = 
  let (terminated, updated_state) = program state
  in case terminated of
       True => Terminated updated_state
       False => Running updated_state
ExecuteStep program (Terminated state) = Terminated state

-- Execute specified number of steps of program on initial state
ExecuteSteps : (program : ProgramType state_type) -> (steps : Nat) -> (initial_state : state_type) -> ExecutionState state_type
ExecuteSteps program Z initial_state = Running initial_state
ExecuteSteps program (S k) initial_state = ExecuteStep program (ExecuteSteps program k initial_state) 

-- A program terminates executing from an initial state if after executing some number of steps it terminates
Terminates : (program : ProgramType state_type) -> (initial_state : state_type) -> (result : state_type) -> Type
Terminates program initial_state result = (num_steps: Nat ** (ExecuteSteps program num_steps initial_state = Terminated result))

-- If termination of program1 implies termination of program2, then we can use program1 wherever we want to use program2
-- (if the only thing we are interested in is the result of program2 terminating).
ImpliesTermination : (program1, program2 : ProgramType state_type) -> Type
ImpliesTermination {state_type} program1 program2 = 
   {initial_state, result : state_type} -> Terminates program1 initial_state result -> Terminates program2 initial_state result

IsNonTerminating : (program : ProgramType state_type) -> (initial_state : state_type) -> Type
IsNonTerminating program initial_state = (num_steps : Nat) -> (state ** ExecuteSteps program num_steps initial_state = Running state)

is_non_terminating_implies_not_terminates : IsNonTerminating program initial_state -> Terminates program initial_state result -> Void
is_non_terminating_implies_not_terminates {program} {initial_state} {result} is_non_terminating terminates = 
  let (num_steps ** terminated_result) = terminates
      e1 = the (ExecuteSteps program num_steps initial_state = Terminated result) terminated_result
      e2 = is_non_terminating num_steps
      (running_state ** e3) = e2
      e4 = the (ExecuteSteps program num_steps initial_state = Running running_state) e3
      e5 = the (Terminated result = Running running_state) $ trans (sym e1) e4
  in running_is_not_terminated $ sym e5
