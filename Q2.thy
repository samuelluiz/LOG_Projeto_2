  theory Q2
    imports
begin 
theorem :
  assumes rpq: "R⟶P∨Q"
and rq: "R⟶¬Q"
shows "R⟶P"
proof ─
  have rp:"R ⟹P "
  proof ─
    assume r: "R"
    from rpq and r have pq: "P∨Q" by (rule impE)
    from rq and r have mq: "¬Q" by (rule impE)
    have ppp: "P⟹P" 
    proof ─
      assume p: "P"
      from p have pp: "P" by ()
    qed
    have qp: "Q⟹P"
    proof ─
      assume q:
