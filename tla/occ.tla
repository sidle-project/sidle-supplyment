--------------------------- MODULE occ ---------------------------
EXTENDS Integers, Sequences, TLC

(* --fair algorithm occ
variables 
    node_ptr = "SlowMem", 
    version = 1,
    is_migrating = FALSE,
    node_lock = FALSE,
    data_in_slow = 10,
    data_in_fast = 0;

process Migrator = "Migrator"
begin
    M_Lock:
        await node_lock = FALSE;
        node_lock := TRUE; 
    M_StartMigrate:
        is_migrating := TRUE; 
    M_CopyData:
        data_in_fast := data_in_slow;
    M_CommitPointer:
        node_ptr := "FastMem";
    M_UpdateVersion:
        \* Migration completed, increment version number
        version := version + 1;
        is_migrating := FALSE;
    M_Unlock:
        node_lock := FALSE;
end process;

process Writer = "Writer"
variables w_val = 20;
begin
    W_Lock:
        await node_lock = FALSE;
        node_lock := TRUE;
    W_Update:
        if node_ptr = "SlowMem" then
            data_in_slow := w_val;
            version := version + 1; 
        end if;
    W_Unlock:
        node_lock := FALSE;
end process;

process Reader = "Reader"
variables r_version = 0, r_val = "", r_data = 0;
begin
    R_BeginRead:
        \* 1. Record the version at the start
        r_version := version;
        if is_migrating = TRUE then goto R_BeginRead; end if;
        
        \* 2. Read data
    R_Read: 
        r_val := node_ptr;
        r_data := IF r_val = "SlowMem" THEN data_in_slow ELSE data_in_fast;
        
    R_Validate:
        \* 3. Validate: If version changed or migrating, must retry
        if (is_migrating = TRUE) \/ (version # r_version) then 
            goto R_BeginRead; 
        else
            \* At this point, can safely assert: the read data is valid at the time of reading
            assert (r_val = "SlowMem" /\ r_data \in {10, 20}) 
                \/ (r_val = "FastMem" /\ r_data \in {10, 20});
        end if;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "7c28162a" /\ chksum(tla) = "f0edf7e2")
VARIABLES pc, node_ptr, version, is_migrating, node_lock, data_in_slow, 
          data_in_fast, w_val, r_version, r_val, r_data

vars == << pc, node_ptr, version, is_migrating, node_lock, data_in_slow, 
           data_in_fast, w_val, r_version, r_val, r_data >>

ProcSet == {"Migrator"} \cup {"Writer"} \cup {"Reader"}

Init == (* Global variables *)
        /\ node_ptr = "SlowMem"
        /\ version = 1
        /\ is_migrating = FALSE
        /\ node_lock = FALSE
        /\ data_in_slow = 10
        /\ data_in_fast = 0
        (* Process Writer *)
        /\ w_val = 20
        (* Process Reader *)
        /\ r_version = 0
        /\ r_val = ""
        /\ r_data = 0
        /\ pc = [self \in ProcSet |-> CASE self = "Migrator" -> "M_Lock"
                                        [] self = "Writer" -> "W_Lock"
                                        [] self = "Reader" -> "R_BeginRead"]

M_Lock == /\ pc["Migrator"] = "M_Lock"
          /\ node_lock = FALSE
          /\ node_lock' = TRUE
          /\ pc' = [pc EXCEPT !["Migrator"] = "M_StartMigrate"]
          /\ UNCHANGED << node_ptr, version, is_migrating, data_in_slow, 
                          data_in_fast, w_val, r_version, r_val, r_data >>

M_StartMigrate == /\ pc["Migrator"] = "M_StartMigrate"
                  /\ is_migrating' = TRUE
                  /\ pc' = [pc EXCEPT !["Migrator"] = "M_CopyData"]
                  /\ UNCHANGED << node_ptr, version, node_lock, data_in_slow, 
                                  data_in_fast, w_val, r_version, r_val, 
                                  r_data >>

M_CopyData == /\ pc["Migrator"] = "M_CopyData"
              /\ data_in_fast' = data_in_slow
              /\ pc' = [pc EXCEPT !["Migrator"] = "M_CommitPointer"]
              /\ UNCHANGED << node_ptr, version, is_migrating, node_lock, 
                              data_in_slow, w_val, r_version, r_val, r_data >>

M_CommitPointer == /\ pc["Migrator"] = "M_CommitPointer"
                   /\ node_ptr' = "FastMem"
                   /\ pc' = [pc EXCEPT !["Migrator"] = "M_UpdateVersion"]
                   /\ UNCHANGED << version, is_migrating, node_lock, 
                                   data_in_slow, data_in_fast, w_val, 
                                   r_version, r_val, r_data >>

M_UpdateVersion == /\ pc["Migrator"] = "M_UpdateVersion"
                   /\ version' = version + 1
                   /\ is_migrating' = FALSE
                   /\ pc' = [pc EXCEPT !["Migrator"] = "M_Unlock"]
                   /\ UNCHANGED << node_ptr, node_lock, data_in_slow, 
                                   data_in_fast, w_val, r_version, r_val, 
                                   r_data >>

M_Unlock == /\ pc["Migrator"] = "M_Unlock"
            /\ node_lock' = FALSE
            /\ pc' = [pc EXCEPT !["Migrator"] = "Done"]
            /\ UNCHANGED << node_ptr, version, is_migrating, data_in_slow, 
                            data_in_fast, w_val, r_version, r_val, r_data >>

Migrator == M_Lock \/ M_StartMigrate \/ M_CopyData \/ M_CommitPointer
               \/ M_UpdateVersion \/ M_Unlock

W_Lock == /\ pc["Writer"] = "W_Lock"
          /\ node_lock = FALSE
          /\ node_lock' = TRUE
          /\ pc' = [pc EXCEPT !["Writer"] = "W_Update"]
          /\ UNCHANGED << node_ptr, version, is_migrating, data_in_slow, 
                          data_in_fast, w_val, r_version, r_val, r_data >>

W_Update == /\ pc["Writer"] = "W_Update"
            /\ IF node_ptr = "SlowMem"
                  THEN /\ data_in_slow' = w_val
                       /\ version' = version + 1
                  ELSE /\ TRUE
                       /\ UNCHANGED << version, data_in_slow >>
            /\ pc' = [pc EXCEPT !["Writer"] = "W_Unlock"]
            /\ UNCHANGED << node_ptr, is_migrating, node_lock, data_in_fast, 
                            w_val, r_version, r_val, r_data >>

W_Unlock == /\ pc["Writer"] = "W_Unlock"
            /\ node_lock' = FALSE
            /\ pc' = [pc EXCEPT !["Writer"] = "Done"]
            /\ UNCHANGED << node_ptr, version, is_migrating, data_in_slow, 
                            data_in_fast, w_val, r_version, r_val, r_data >>

Writer == W_Lock \/ W_Update \/ W_Unlock

R_BeginRead == /\ pc["Reader"] = "R_BeginRead"
               /\ r_version' = version
               /\ IF is_migrating = TRUE
                     THEN /\ pc' = [pc EXCEPT !["Reader"] = "R_BeginRead"]
                     ELSE /\ pc' = [pc EXCEPT !["Reader"] = "R_Read"]
               /\ UNCHANGED << node_ptr, version, is_migrating, node_lock, 
                               data_in_slow, data_in_fast, w_val, r_val, 
                               r_data >>

R_Read == /\ pc["Reader"] = "R_Read"
          /\ r_val' = node_ptr
          /\ r_data' = (IF r_val' = "SlowMem" THEN data_in_slow ELSE data_in_fast)
          /\ pc' = [pc EXCEPT !["Reader"] = "R_Validate"]
          /\ UNCHANGED << node_ptr, version, is_migrating, node_lock, 
                          data_in_slow, data_in_fast, w_val, r_version >>

R_Validate == /\ pc["Reader"] = "R_Validate"
              /\ IF (is_migrating = TRUE) \/ (version # r_version)
                    THEN /\ pc' = [pc EXCEPT !["Reader"] = "R_BeginRead"]
                    ELSE /\ Assert(   (r_val = "SlowMem" /\ r_data \in {10, 20})
                                   \/ (r_val = "FastMem" /\ r_data \in {10, 20}), 
                                   "Failure of assertion at line 67, column 13.")
                         /\ pc' = [pc EXCEPT !["Reader"] = "Done"]
              /\ UNCHANGED << node_ptr, version, is_migrating, node_lock, 
                              data_in_slow, data_in_fast, w_val, r_version, 
                              r_val, r_data >>

Reader == R_BeginRead \/ R_Read \/ R_Validate

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Migrator \/ Writer \/ Reader
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
-------------------------------------------------------------------------
StateConstraint == version < 4

TypeOK == 
    /\ node_ptr \in {"SlowMem", "FastMem"}
    /\ version \in Nat
    /\ is_migrating \in BOOLEAN
    /\ node_lock \in BOOLEAN
    /\ data_in_slow \in Int
    /\ data_in_fast \in Int
    \* These are now scalars because we used process Reader = "Reader" instead of a set
    /\ r_val \in STRING \cup {""}
    /\ r_data \in Int
    /\ w_val \in Int
    /\ pc \in [ {"Migrator", "Writer", "Reader"} -> STRING ]

\* 2. Core: Verify correctness of concurrent writes
\* Ensure that after migration, the data in the new node is either the initial value 10 or the updated 20, never 0 (memcpy failure)
WriterConsistency == 
    (node_ptr = "FastMem") => (data_in_fast \in {10, 20})

\* 3. Verify if mutual exclusion lock is effective
\* When migrator copies data, writer must not be in W_Write state
LockSafety == 
    (pc["Migrator"] = "M_CopyData") => (pc["Writer"] # "W_Write")

=========================================================================
