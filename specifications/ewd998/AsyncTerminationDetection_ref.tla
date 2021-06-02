---------------------- MODULE AsyncTerminationDetection_ref ---------------------
EXTENDS AsyncTerminationDetection

\* With the module SyncTerminationDetection defined in 
\* ../ewd840/SyncTerminationDetection.tla
STD == 
    INSTANCE SyncTerminationDetection 
    WITH active <- [n \in Node |-> active[n] \/ pending[n] > 0]

\* Make TLC happy, ie., 'STD!Spec' not valid in MC.cfg.
STDSpec == STD!Spec

THEOREM Spec => STDSpec

=============================================================================
\* Modification History
\* Last modified Wed June 2 15:19:20 CET 2021 by Markus Kuppe
\* Created Wed June 2 15:19:20 CET 2021 by Markus Kuppe
