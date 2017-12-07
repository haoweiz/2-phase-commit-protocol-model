----------------------------- MODULE t2pc -----------------------------
EXTENDS Integers,Sequences,FiniteSets,TLC
CONSTANTS RM,                  \* The number of resource managers. 
          BTM,                 \* Whether have backupTM.           
          RMMAYFAIL,           \* Whether RM could fail.           
          TMMAYFAIL            \* Whether TM could fail.           
          
          
          
          
(*          
--algorithm TransactionCommit{
  variable rmState = [rm \in RM |->"working"],
           tmState = "init";                            \* tmState's init state.    
           btmState = "init";                           \* backupTM's init state.
  define{
    canCommit == \A rm \in RM : rmState[rm] \in {"prepared","committed"} \*If some rm are commited or all rm are commited, 
                                                                         \*which means tmState is "commit", sowe can commit.
    canAbort == \A rm \in RM : rmState[rm] # "committed"  \*if no rm are committed, we don't know the state of tmState, 
                                                          \*if tmState is not "commit", we cannot commit.
    }
    
  macro Prepare(p){
    await rmState[p] = "working";  \*if rmState[p] is working, then it will be prepared
      rmState[p] :="prepared";
    }
    
  macro Decide(p){
    either {await rmState[p] = "prepared" /\ canCommit /\ (tmState = "commit" \/ btmState = "commit");     \*If rmState[p] is prepared, some rm is committed and 
                                                                                                           \*if we have backupTM, either tmState or btmState is "commit",
                                                                                                           \*then we can change rmState to "commit". 
            rmState[p] := "committed";
           }
    or     {await rmState[p] \in {"working","prepared"} /\ canAbort;                                      \*If not all rmState is committed, we can abort at any time.
            rmState[p] := "abort"
           }
  }
  
  macro Fail(p){
     if(RMMAYFAIL)  rmState[p] := "crash"                                \*If RMMAYFAIL, rmState[p] could be "crash"
  }
  
  fair process(RManager \in RM){                                          \*If rmState is working or prepared, it should execute until abort or commit if we
    RS:while(rmState[self] \in {"working","prepared"}){                   \*set up backupTM. Otherwise termination might be violated.
         either Prepare(self) or Decide(self) or Fail(self)}
  }
  
  fair process(TManager = 0){                                              \*If all rm are prepared, it's time to commit, so set tmState to commit.
  TS:either{await canCommit;
         TC:tmState := "commit";
            if(BTM) btmState := "commit";                                  \*If we set backupTM, change the btmState just the same as tmState.
         F1:if(TMMAYFAIL) tmState := "hidden";}
         
     or{await canAbort;                                                    \*Abort can appear any time unless all rmState are committed.
       TA:tmState := "abort";
            if(BTM) btmState := "abort";                                   \*If we set backupTM, change the btmState just the same as tmState.
       F2:if(TMMAYFAIL) tmState := "hidden";}
   }
}
*)
\* BEGIN TRANSLATION
VARIABLES rmState, tmState, btmState, pc

(* define statement *)
canCommit == \A rm \in RM : rmState[rm] \in {"prepared","committed"}

canAbort == \A rm \in RM : rmState[rm] # "committed"


vars == << rmState, tmState, btmState, pc >>

ProcSet == (RM) \cup {0}

Init == (* Global variables *)
        /\ rmState = [rm \in RM |->"working"]
        /\ tmState = "init"
        /\ btmState = "init"
        /\ pc = [self \in ProcSet |-> CASE self \in RM -> "RS"
                                        [] self = 0 -> "TS"]

RS(self) == /\ pc[self] = "RS"
            /\ IF rmState[self] \in {"working","prepared"}
                  THEN /\ \/ /\ rmState[self] = "working"
                             /\ rmState' = [rmState EXCEPT ![self] = "prepared"]
                          \/ /\ \/ /\ rmState[self] = "prepared" /\ canCommit /\ (tmState = "commit" \/ btmState = "commit")
                                   /\ rmState' = [rmState EXCEPT ![self] = "committed"]
                                \/ /\ rmState[self] \in {"working","prepared"} /\ canAbort
                                   /\ rmState' = [rmState EXCEPT ![self] = "abort"]
                          \/ /\ IF RMMAYFAIL
                                   THEN /\ rmState' = [rmState EXCEPT ![self] = "crash"]
                                   ELSE /\ TRUE
                                        /\ UNCHANGED rmState
                       /\ pc' = [pc EXCEPT ![self] = "RS"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED rmState
            /\ UNCHANGED << tmState, btmState >>

RManager(self) == RS(self)

TS == /\ pc[0] = "TS"
      /\ \/ /\ canCommit
            /\ pc' = [pc EXCEPT ![0] = "TC"]
         \/ /\ canAbort
            /\ pc' = [pc EXCEPT ![0] = "TA"]
      /\ UNCHANGED << rmState, tmState, btmState >>

TC == /\ pc[0] = "TC"
      /\ tmState' = "commit"
      /\ IF BTM
            THEN /\ btmState' = "commit"
            ELSE /\ TRUE
                 /\ UNCHANGED btmState
      /\ pc' = [pc EXCEPT ![0] = "F1"]
      /\ UNCHANGED rmState

F1 == /\ pc[0] = "F1"
      /\ IF TMMAYFAIL
            THEN /\ tmState' = "hidden"
            ELSE /\ TRUE
                 /\ UNCHANGED tmState
      /\ pc' = [pc EXCEPT ![0] = "Done"]
      /\ UNCHANGED << rmState, btmState >>

TA == /\ pc[0] = "TA"
      /\ tmState' = "abort"
      /\ IF BTM
            THEN /\ btmState' = "abort"
            ELSE /\ TRUE
                 /\ UNCHANGED btmState
      /\ pc' = [pc EXCEPT ![0] = "F2"]
      /\ UNCHANGED rmState

F2 == /\ pc[0] = "F2"
      /\ IF TMMAYFAIL
            THEN /\ tmState' = "hidden"
            ELSE /\ TRUE
                 /\ UNCHANGED tmState
      /\ pc' = [pc EXCEPT ![0] = "Done"]
      /\ UNCHANGED << rmState, btmState >>

TManager == TS \/ TC \/ F1 \/ TA \/ F2

Next == TManager
           \/ (\E self \in RM: RManager(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in RM : WF_vars(RManager(self))
        /\ WF_vars(TManager)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

consistency == tmState = "commit" => \A i \in RM : rmState[i] # "abort"      
            /\ tmState = "abort" => \A j \in RM : rmState[j] # "committed" 
            /\ tmState = "hidden" => \A k \in RM : rmState[k] # "committed"
terminate == <>(\A i \in RM : rmState[i] \in {"committed","abort","crash"})

=============================================================================
\*1.2 TMMAYFAIL is true and RMMAYFAIL is false means tmState could be "hidden" and rmState cannot be
\*hidden. In this situation, termination will be violated. For example, when TM is "commit" and some 
\*RM are committed, then TM crashed while some other RM is prepared, but they can never be "commit" or abort
\*because TM is "hidden" now. That's why we get result when RM equals 3 that <<"committed","prepared","committed">>.
\*It will never been terminated because "prepared" has no way to "commit".

\*1.3 Termination and comsistency remain true. The states cancommit and canabort is owned by both BTM and TM.
\* So when TM crashes, the RMs can still consult the BTM and make their decision. 
\*If an RM crashed, then all other RMs can only abort. So all other uncrashed RMs remain consistent.

\* Modification History
\* Last modified Tue Dec 05 19:49:37 EST 2017 by lenovo
\* Created Wed Nov 29 17:13:20 EST 2017 by lenovo
