import Paper20.FastHilbert
namespace Paper20.HilbertChunks

/-- The complete contribution of a fixed initial partition prefix. The fuel
is exactly the one reached by the original 43-partition recursion. -/
def prefixTotal (pre : List ℕ) : List ℕ :=
  ((partitionsCappedAux (44-pre.length) (pre.getLastD 43) (43-pre.sum)).map
    (fun tail => pre++tail)).foldl
      (FastHilbert.addPart 43 1 903) (List.replicate 904 0)

end Paper20.HilbertChunks
