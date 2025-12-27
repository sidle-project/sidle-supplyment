---- MODULE lockfree ----
EXTENDS Integers, Sequences, TLC

(* --fair algorithm lockfree 
variables 
    mapping_table = 1,          \* Initially points to memory address 1
    mem_pool_A = [i \in 1..20 |-> 0], \* Simulates pool A
    mem_pool_B = [i \in 21..40 |-> 0], \* Simulates pool B (Target)
    retired = {},
    next_A = 2,                 \* Next available address in pool A
    next_B = 21;                \* Next available address in pool B
    max_seen_val = 0;

define
    \* Invariant: The address pointed to by the mapping table should never be in the retired set
    NoUseAfterFree == mapping_table \notin retired
    
   \* Data consistency: Values should be non-decreasing, migration should not cause rollback
    DataCorrectness ==  
        LET current_val == IF mapping_table < 21 
                           THEN mem_pool_A[mapping_table] 
                           ELSE mem_pool_B[mapping_table]
        IN current_val >= max_seen_val
end define;

\* Migration process: Moves from Pool A to Pool B
process Migrator = 0
variables old_addr = 0, new_addr = 0, val = 0, done = FALSE;
begin
M_Start:
    while done = FALSE do
        old_addr := mapping_table;
        \* Simulates reading content
        val := IF old_addr < 21 THEN mem_pool_A[old_addr] ELSE mem_pool_B[old_addr];
        
        \* Simulates allocation to Pool B (Target)
        new_addr := next_B;
        next_B := next_B + 1;
        mem_pool_B[new_addr] := val;
        
    M_CAS:
        if mapping_table = old_addr then
            mapping_table := new_addr;
            retired := retired \cup {old_addr};
            max_seen_val := val;
            done := TRUE; \* Exit loop after success
        else
            \* CAS failed, Writer preempted, retry
            skip; 
        end if;
    end while;
end process;

\* Writer process: Produces delta updates in Pool A
process Writer \in 1..2
variables old_ptr = 0, new_ptr = 0, current_val = 0, count = 0;
begin
W_Start:
    \* Each Writer attempts to update 2 times
    while count < 2 do
        old_ptr := mapping_table;
        current_val := IF old_ptr < 21 THEN mem_pool_A[old_ptr] ELSE mem_pool_B[old_ptr];
        
        \* Writer always allocates in Pool A
        new_ptr := next_A;
        next_A := next_A + 1;
        mem_pool_A[new_ptr] := current_val + 1;
        
    W_CAS:
        if mapping_table = old_ptr then
            mapping_table := new_ptr;
            retired := retired \cup {old_ptr};
            count := count + 1;
            max_seen_val := val;
        else
            \* Failure retry
            skip;
        end if;
    end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "7c28162a" /\ chksum(tla) = "a1521543")
VARIABLES pc, mapping_table, mem_pool_A, mem_pool_B, retired, next_A, next_B, 
          max_seen_val

(* define statement *)
NoUseAfterFree == mapping_table \notin retired


DataCorrectness ==
    LET current_val == IF mapping_table < 21
                       THEN mem_pool_A[mapping_table]
                       ELSE mem_pool_B[mapping_table]
    IN current_val >= max_seen_val

VARIABLES old_addr, new_addr, val, done, old_ptr, new_ptr, current_val, count

vars == << pc, mapping_table, mem_pool_A, mem_pool_B, retired, next_A, next_B, 
           max_seen_val, old_addr, new_addr, val, done, old_ptr, new_ptr, 
           current_val, count >>

ProcSet == {0} \cup (1..2)

Init == (* Global variables *)
        /\ mapping_table = 1
        /\ mem_pool_A = [i \in 1..20 |-> 0]
        /\ mem_pool_B = [i \in 21..40 |-> 0]
        /\ retired = {}
        /\ next_A = 2
        /\ next_B = 21
        /\ max_seen_val = 0
        (* Process Migrator *)
        /\ old_addr = 0
        /\ new_addr = 0
        /\ val = 0
        /\ done = FALSE
        (* Process Writer *)
        /\ old_ptr = [self \in 1..2 |-> 0]
        /\ new_ptr = [self \in 1..2 |-> 0]
        /\ current_val = [self \in 1..2 |-> 0]
        /\ count = [self \in 1..2 |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "M_Start"
                                        [] self \in 1..2 -> "W_Start"]

M_Start == /\ pc[0] = "M_Start"
           /\ IF done = FALSE
                 THEN /\ old_addr' = mapping_table
                      /\ val' = (IF old_addr' < 21 THEN mem_pool_A[old_addr'] ELSE mem_pool_B[old_addr'])
                      /\ new_addr' = next_B
                      /\ next_B' = next_B + 1
                      /\ mem_pool_B' = [mem_pool_B EXCEPT ![new_addr'] = val']
                      /\ pc' = [pc EXCEPT ![0] = "M_CAS"]
                 ELSE /\ pc' = [pc EXCEPT ![0] = "Done"]
                      /\ UNCHANGED << mem_pool_B, next_B, old_addr, new_addr, 
                                      val >>
           /\ UNCHANGED << mapping_table, mem_pool_A, retired, next_A, 
                           max_seen_val, done, old_ptr, new_ptr, current_val, 
                           count >>

M_CAS == /\ pc[0] = "M_CAS"
         /\ IF mapping_table = old_addr
               THEN /\ mapping_table' = new_addr
                    /\ retired' = (retired \cup {old_addr})
                    /\ max_seen_val' = val
                    /\ done' = TRUE
               ELSE /\ TRUE
                    /\ UNCHANGED << mapping_table, retired, max_seen_val, done >>
         /\ pc' = [pc EXCEPT ![0] = "M_Start"]
         /\ UNCHANGED << mem_pool_A, mem_pool_B, next_A, next_B, old_addr, 
                         new_addr, val, old_ptr, new_ptr, current_val, count >>

Migrator == M_Start \/ M_CAS

W_Start(self) == /\ pc[self] = "W_Start"
                 /\ IF count[self] < 2
                       THEN /\ old_ptr' = [old_ptr EXCEPT ![self] = mapping_table]
                            /\ current_val' = [current_val EXCEPT ![self] = IF old_ptr'[self] < 21 THEN mem_pool_A[old_ptr'[self]] ELSE mem_pool_B[old_ptr'[self]]]
                            /\ new_ptr' = [new_ptr EXCEPT ![self] = next_A]
                            /\ next_A' = next_A + 1
                            /\ mem_pool_A' = [mem_pool_A EXCEPT ![new_ptr'[self]] = current_val'[self] + 1]
                            /\ pc' = [pc EXCEPT ![self] = "W_CAS"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                            /\ UNCHANGED << mem_pool_A, next_A, old_ptr, 
                                            new_ptr, current_val >>
                 /\ UNCHANGED << mapping_table, mem_pool_B, retired, next_B, 
                                 max_seen_val, old_addr, new_addr, val, done, 
                                 count >>

W_CAS(self) == /\ pc[self] = "W_CAS"
               /\ IF mapping_table = old_ptr[self]
                     THEN /\ mapping_table' = new_ptr[self]
                          /\ retired' = (retired \cup {old_ptr[self]})
                          /\ count' = [count EXCEPT ![self] = count[self] + 1]
                          /\ max_seen_val' = val
                     ELSE /\ TRUE
                          /\ UNCHANGED << mapping_table, retired, max_seen_val, 
                                          count >>
               /\ pc' = [pc EXCEPT ![self] = "W_Start"]
               /\ UNCHANGED << mem_pool_A, mem_pool_B, next_A, next_B, 
                               old_addr, new_addr, val, done, old_ptr, new_ptr, 
                               current_val >>

Writer(self) == W_Start(self) \/ W_CAS(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Migrator
           \/ (\E self \in 1..2: Writer(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
=========================================================================
