import Lean.Meta.Tactic.Simp.RegisterCommand

/-- Exact rewrites used to reduce an imported MIR instruction before assembling
its shared whole-body verification condition. -/
register_simp_attr miri_initial_wp
