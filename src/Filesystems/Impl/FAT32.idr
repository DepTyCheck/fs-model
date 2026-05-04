module Filesystems.Impl.FAT32

import Filesystems.Node
import Filesystems.Node.Index
import Filesystems.NodeOps
import Filesystems.Impl.Posix
import Data.Nat
import Data.Nat.Division
import Data.DPair
import Data.Vect
import Data.SnocVect
import Data.SnocVect.Quantifiers
import Derive.Prelude

%default total
%prefix_record_projections off
%language ElabReflection

namespace Constants
    public export
    DirentSize : Nat
    DirentSize = 32

    public export
    FilenameLengthName : Nat
    FilenameLengthName = 8

    public export
    FilenameLengthExt : Nat
    FilenameLengthExt = 3

    public export
    FilenameLength : Nat
    FilenameLength = FilenameLengthName + FilenameLengthExt

public export
record Metadata where
    constructor MkMetadata
    readOnly : Bool
    hidden : Bool
    system : Bool
    archive : Bool

public export
DefaultFileMeta Metadata where
    defaultFileMeta = MkMetadata False False False False

public export
DefaultDirMeta Metadata where
    defaultDirMeta = MkMetadata False False False False

public export
FileWritable Metadata where
    isWritable meta = not meta.readOnly

public export
0 MetadataSelector : RootLabel -> Type
MetadataSelector IsRoot = Unit
MetadataSelector NotRoot = Metadata

public export
data NodeCfg : Type where
    MkNodeCfg : (clustSize : Nat) ->               -- bytes per cluster
-- NOTE: clustSize must not be greater than 32K
                (0 clustNZ : IsSucc clustSize) =>
                NodeCfg

public export
record NodeArgs where
    constructor MkNodeArgs
    cur : Nat
    tot : Nat
    {auto 0 curTotLTE : LTE cur tot}

public export
data Filename : Type where
    MkFilename : Vect FilenameLength Bits8 -> Filename
%runElab derive "Filename" [Show, Eq]

public export
0 FsNode' : RootLabel -> Type
FsNode' = FsNode MetadataSelector Filename

public export
0 FsEntries' : SnocVect k Presence -> Type
FsEntries' prs = FsEntries prs MetadataSelector Filename

public export
0 UniqNames' : SnocVect k Presence -> Type
UniqNames' prs = UniqNames prs Filename

public export
totsum : SnocVect k NodeArgs -> Nat
totsum ars = sum $ (.tot) <$> ars

public export
data Node : NodeCfg -> NodeArgs -> FsNode' rootl -> Type

public export
data MaybeNode : NodeCfg -> NodeArgs -> MaybeP pr (FsNode' NotRoot) -> Type where
    Nothing : MaybeNode cfg (MkNodeArgs 0 0 @{LTEZero}) Nothing
    Just : Node cfg ar ent -> MaybeNode cfg ar (Just ent)

public export
0 FAT32Entries : NodeCfg -> SnocVect k NodeArgs -> (prs : SnocVect k Presence) -> FsEntries' prs -> Type
FAT32Entries cfg ars prs ents = All (\(ar, Element pr ent) => MaybeNode cfg ar ent) (zip ars $ pushIn prs ents) 

data Node : NodeCfg -> NodeArgs -> FsNode' rootl -> Type where
    File : (0 clustNZ : IsSucc clustSize) =>
           (meta : Metadata) ->
           (blob : SnocVect k Bits8) ->
           Node (MkNodeCfg clustSize) (MkNodeArgs (divCeilNZ' k clustSize) (divCeilNZ' k clustSize) @{Relation.reflexive}) (File meta blob)
    Dir  : forall clustSize.
           (0 clustNZ : IsSucc clustSize) =>           
           (meta : Metadata) ->
           {0 prs : SnocVect k Presence} ->
           (names : UniqNames' prs) ->
           {0 ents : FsEntries' prs} ->
           (entries : FAT32Entries cfg ars prs ents) ->
           Node (MkNodeCfg clustSize) (
               MkNodeArgs (divCeilNZ' (DirentSize * (2 + k)) clustSize) (divCeilNZ' (DirentSize * (2 + k)) clustSize + totsum ars) @{lteAddRight (divCeilNZ' (DirentSize * (2 + k)) clustSize) {m = totsum ars}}
           ) (Dir meta names ents)
    Root : forall clustSize.
           (0 clustNZ : IsSucc clustSize) =>
           {0 k : Nat} ->
           {0 prs : SnocVect k Presence} ->
           (names : UniqNames' prs) ->
           {0 ars : SnocVect k NodeArgs} ->
           {0 ents : FsEntries' prs} ->
           (entries : FAT32Entries cfg ars prs ents) ->
           Node (MkNodeCfg clustSize) (
               let cur' = divCeilNZ' (DirentSize * k) clustSize
               in MkNodeArgs cur' (cur' + totsum ars) @{lteAddRight cur' {m = totsum ars}}
           ) (Root () names ents)

setFlags : (node : FsNode' rootl) -> IndexIn node NotRoot dirl -> Metadata -> FsNode' rootl
setFlags node idx meta' with (indexGet node idx)
  _ | (Element (File _ blob) _) = indexSet node idx $ File meta' blob
  _ | (Element (Dir _ names entries) _) = indexSet node idx $ Dir meta' names entries

public export
data FAT32OnlyOps : FsOpsType MetadataSelector Filename where
    GetFlags : (idx : IndexIn root rootl dirl) ->
               FAT32OnlyOps root root
    SetFlags : (idx : IndexIn root NotRoot dirl) ->
               (meta : Metadata) ->
               FAT32OnlyOps root $ setFlags _ idx meta

public export
0 FAT32Ops : FsOpsType MetadataSelector Filename
FAT32Ops = PosixOps |+| FAT32OnlyOps

public export
0 FAT32OpsSeq : FsNode' IsRoot -> Type
FAT32OpsSeq = FsOpsSeq FAT32Ops
