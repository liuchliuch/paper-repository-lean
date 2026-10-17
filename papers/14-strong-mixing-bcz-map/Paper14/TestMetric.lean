import Paper14.Basic
namespace Paper14
example (x y : ℝ × ℝ) : dist x y = max (dist x.1 y.1) (dist x.2 y.2) :=
  Prod.dist_eq
end Paper14
