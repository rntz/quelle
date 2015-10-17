(person :=
  (constable)
  (harper)
  (arbob)
  (licata))

(advisor :=
  (constable harper)
  (harper arbob)
  (harper licata))

((ancestor X X) :- (person X))
((ancestor X Z) :- (advisor X Y) (ancestor Y Z))
