---- MODULE MC ----
EXTENDS t2pc, TLC

\* CONSTANT definitions @modelParameterConstants:0BTM
const_1512521541080336000 == 
TRUE
----

\* CONSTANT definitions @modelParameterConstants:1RMMAYFAIL
const_1512521541080337000 == 
TRUE
----

\* CONSTANT definitions @modelParameterConstants:2TMMAYFAIL
const_1512521541080338000 == 
TRUE
----

\* CONSTANT definitions @modelParameterConstants:3RM
const_1512521541080339000 == 
1..3
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1512521541080340000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1512521541080341000 ==
consistency
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1512521541080342000 ==
Termination
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_1512521541080343000 ==
terminate
----
=============================================================================
\* Modification History
\* Created Tue Dec 05 19:52:21 EST 2017 by lenovo
