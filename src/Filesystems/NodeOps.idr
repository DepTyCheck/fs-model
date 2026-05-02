module Filesystems.NodeOps

import Filesystems.Node

%default total
%prefix_record_projections off

public export
0 FsOpsType : (RootLabel -> Type) -> Type -> Type
FsOpsType mty fty = FsNode mty fty IsRoot -> FsNode mty fty IsRoot -> Type

export infixl 8 |+|
public export
(|+|) : FsOpsType mty fty -> FsOpsType mty fty -> FsOpsType mty fty
(|+|) l r pred f = Either (l pred f) (r pred f)

namespace FsOpsSeq
  public export
  data FsOpsSeq : FsOpsType mty fty -> FsNode mty fty IsRoot -> Type where
    Nil : {0 no : FsOpsType mty fty} ->
          FsOpsSeq no st
    (::) : {0 no : FsOpsType mty fty} ->
           (op : no f t) ->
           (cont : FsOpsSeq no t) ->
           FsOpsSeq no f
