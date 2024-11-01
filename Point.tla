------------------------------- MODULE Point -------------------------------
\* File > Open Module > Add TLA+ Module
LOCAL INSTANCE Integers
CONSTANTS X, Y
ASSUME X \in Int
ASSUME Y \in Int
Point == <<X, Y>>
AddPoint(x, y) == <<X + x, Y + y>>
=============================================================================
\* Modification History
\* Last modified Fri Nov 01 14:30:39 GMT 2024 by frankeg
\* Created Fri Nov 01 14:25:35 GMT 2024 by frankeg
