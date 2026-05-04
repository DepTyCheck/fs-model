module Equiv

import Filesystems.Node as F
import Filesystems.Node.Index as FI
import Filesystems.NodeOps as FO
import Filesystems.Impl.FAT32 as G
import Filesystems.Impl.Posix as P
import Data.Nat
import Data.DPair
import Data.Vect
import Data.SnocVect
import Data.SnocVect.Quantifiers

import Filesystems.FAT32 as C
import Filesystems.FAT32.NodeOps as CO
import Filesystems.FAT32.Utils as CU
import Data.Monomorphic.Vect as MV

%default total
%prefix_record_projections off
%hide Data.Nat.divCeilNZ

public export
Cast G.NodeCfg C.NodeCfg where
    cast (MkNodeCfg clustSize) = MkNodeCfg clustSize

public export
Cast C.NodeCfg G.NodeCfg where
    cast (MkNodeCfg clustSize) = MkNodeCfg clustSize

public export
Cast G.NodeArgs C.NodeArgs where
    cast (MkNodeArgs cur tot) = MkNodeArgs cur tot

public export
Cast C.NodeArgs G.NodeArgs where
    cast (MkNodeArgs curS totS) = MkNodeArgs curS totS

public export
Cast (SnocVect k G.NodeArgs) (SnocVectNodeArgs k) where
    cast [<] = [<]
    cast (sx :< x) = cast sx :< cast x

public export
Cast (SnocVectNodeArgs k) (SnocVect k G.NodeArgs) where
    cast [<] = [<]
    cast (sx :< x) = cast sx :< cast x

public export
Cast F.Presence MV.Presence where
    cast Absent = Absent
    cast Present = Present

public export
Cast MV.Presence F.Presence where
    cast Absent = Absent
    cast Present = Present

public export
Cast (SnocVect k F.Presence) (SnocVectPresence k) where
    cast [<] = [<]
    cast (sx :< x) = cast sx :< cast x

public export
Cast (SnocVectPresence k) (SnocVect k F.Presence) where
    cast [<] = [<]
    cast (sx :< x) = cast sx :< cast x

public export
Cast F.RootLabel C.RootLabel where
    cast IsRoot = Rootful
    cast NotRoot = Rootless

public export
Cast C.RootLabel F.RootLabel where
    cast Rootful = IsRoot
    cast Rootless = NotRoot

public export
Cast G.Metadata C.Metadata where
    cast (MkMetadata readOnly hidden system archive) = MkMetadata readOnly hidden system archive

public export
Cast C.Metadata G.Metadata where
    cast (MkMetadata readOnly hidden system archive) = MkMetadata readOnly hidden system archive

public export
Cast (VectBits8 k) (Vect k Bits8) where
    cast [] = []
    cast (x :: xs) = x :: cast xs

public export
Cast (Vect k Bits8) (VectBits8 k) where
    cast [] = []
    cast (x :: xs) = x :: cast xs

public export
Cast (SnocVectBits8 k) (SnocVect k Bits8) where
    cast [<] = [<]
    cast (sx :< x) = cast sx :< x

public export
Cast (SnocVect k Bits8) (SnocVectBits8 k) where
    cast [<] = [<]
    cast (sx :< x) = cast sx :< x

public export
totsumEq : (ars : SnocVect k G.NodeArgs) -> G.totsum {k} ars = SnocVectNodeArgs.totsum {k} (cast ars) 
totsumEq [<] = Refl
totsumEq (sx :< (MkNodeArgs cur tot)) = do
    let u = cong (+ tot) $ totsumEq sx
    u `trans` plusCommutative _ _

public export
g2cEntries : FAT32Entries cfg {k} ars prs ents -> HSnocVectMaybeNode (cast cfg) k (cast ars) (cast prs)
g2cEntries x with 0 (zip ars $ pushIn prs ents)
  g2cEntries [<] | [<] with 0 (ars)
    g2cEntries [<] | [<] | aaaa = ?aaa_rhsa_rhsa
  g2cEntries (psx :< px) | (zsx :< zx) = ?bbb

public export
g2cImage : {0 fs : FsNode' rootl} -> G.Node cfg ar fs -> C.Node.Node (cast cfg) (cast ar) (cast rootl)
g2cImage (File meta blob) = rewrite sym $ lengthCorrect blob in File {k = length blob} (cast meta) (rewrite lengthCorrect blob in cast blob)
g2cImage (Dir {clustSize} @{clustNZ} {k=kb} {ars} {prs} {ents} meta names entries) = do
    rewrite totsumEq ars
    rewrite sym $ lengthCorrect entries
    Dir {k = length entries} (cast meta) (g2cEntries $ rewrite lengthCorrect entries in entries) (?cc names)
g2cImage (Root names entries) = ?g2cImage_rhs_2

public export
c2generic : C.Node.Node cfg ar rootl -> FsNode' $ cast rootl

public export
c2gImage : (img : C.Node.Node cfg ar rootl) -> G.Node (cast cfg) (cast ar) (c2generic img)

public export
g2gImageEq : (img : G.Node cfg ar fs) -> c2gImage (g2cImage img) ~=~ img

public export
c2cImageEq : (img : C.Node.Node cfg ar rootl) -> g2cImage (c2gImage img) ~=~ img

public export
g2cOps : (fs : FsNode' IsRoot) -> (img : G.Node cfg ar fs) -> FAT32OpsSeq fs -> NodeOps (cast cfg) (g2cImage img)

public export
c2gOps : (img : C.Node.Node cfg ar Rootful) -> NodeOps cfg img -> FAT32OpsSeq (c2generic img)

public export
g2gOpsEq : (fs : FsNode' IsRoot) -> (img : G.Node cfg ar fs) -> (ops : FAT32OpsSeq fs) -> c2gOps _ (g2cOps fs img ops) ~=~ ops

public export
c2cOpsEq : (img : C.Node.Node cfg ar Rootful) -> (ops : NodeOps cfg img) -> g2cOps _ (c2gImage img) (c2gOps img ops) ~=~ ops

