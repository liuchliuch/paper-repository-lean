import Paper23.BoundingSupport
import Paper23.CertificateBucketMerge

/-! Semantics for the large integer bounding checks. Buckets reorganize the
same original labelled cubical chains; every candidate merge is still checked
by ordinary Lean kernel reduction. -/
namespace Paper23.Bounding
open Cubical CertificateChecks

/-- A checked bucket merge adds its actual source and target cubical chains. -/
theorem bucket_node_sound (left right normal : BucketVector)
    (ls rs lt rt : RawChain)
    (hl : bucketChain left = boundary ls + (-6 : ℤ) • lt)
    (hr : bucketChain right = boundary rs + (-6 : ℤ) • rt)
    (checked : mergeBuckets left right = normal) :
    bucketChain normal = boundary (ls + rs) + (-6 : ℤ) • (lt + rt) := by
  rw [← checked, bucketChain_mergeBuckets, hl, hr, map_add, smul_add]
  abel

/-- Converting an already checked flat normal form to buckets retains its
boundary equation in the original cubical chain group. -/
theorem packed_node_sound (normal : List (ℕ × ℤ)) (source target : RawChain)
    (h : codeChain normal = boundary source + (-6 : ℤ) • target) :
    bucketChain (packBuckets normal) = boundary source + (-6 : ℤ) • target :=
  (bucketChain_packBuckets normal).trans h

end Paper23.Bounding
