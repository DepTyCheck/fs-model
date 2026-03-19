module Filesystems.NodeOps

import Filesystems.Node

%default total
%prefix_record_projections off

public export
0 FsNodeOp : Type
FsNodeOp = {0 mty : RootLabel -> Type} -> {0 fty : Type} -> FsNode mty fty IsRoot -> FsNode mty fty IsRoot -> Type

namespace FsNodeOps
  public export
  data FsNodeOps : FsNodeOp -> FsNode mty fty IsRoot -> Type where
    Nil : {0 no : FsNodeOp} ->
          FsNodeOps no st
    (::) : {0 no : FsNodeOp} ->
           (op : no f t) ->
           (cont : FsNodeOps no t) ->
           FsNodeOps no f

export infixl 8 |+|
public export
(|+|) : FsNodeOp -> FsNodeOp -> FsNodeOp
(|+|) l r pred f = Either (l pred f) (r pred f)
