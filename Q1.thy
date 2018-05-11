 theory Q1
    imports Main
begin 
theorem abba : "(A∧B) ⟶ (B∧A)"
proof -
  have ab:"(A∧B) ⟹ (B∧A) "
  proof -
    assume ab: "A∧B"
    from ab have a: "A" by (rule conjE)
    from ab have b: "B" by (rule conjE)
    from b and a show  ba: "B∧A" by (rule conjI)
  qed
  from ab show "(A∧B)⟶(B∧A)" by (rule impI)
qed
end
