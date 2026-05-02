module Filesystems.Node.Index

import Data.DPair
import Data.SnocVect
import Data.SnocVect.Quantifiers
import Filesystems.Node

%default total
%prefix_record_projections off

public export
data IdxDirLabel = FileI | DirI

namespace FsEntries
    public export
    data IndexIn : FsEntries prs mty fty -> IdxDirLabel -> Type

    public export
    data AtIndex : {sx : FsEntries prs mty fty} -> (idx : IndexIn sx dirl) -> FsNode mty fty fs' -> Type

    public export
    Uninhabited (FsEntries.AtIndex {dirl = FileI} idx (Dir meta names ents))
    
    public export
    Uninhabited (FsEntries.AtIndex {dirl = DirI} idx (File meta blob))
    
    public export
    indexGet : (sx : FsEntries prs mty fty) -> (idx : IndexIn sx dirl) -> Subset (FsNode mty fty NotRoot) (\nd => AtIndex idx nd)
    
    public export
    indexSet : (sx : FsEntries prs mty fty) ->
               (idx : IndexIn sx dirl) ->
               FsNode mty fty NotRoot ->
               FsEntries prs mty fty
    
    public export
    data NamesWeakened : {0 prs : SnocVect k Presence} -> (ff : UniqNames prs fty) -> {0 prs' : SnocVect k Presence} -> (ff' : UniqNames prs' fty) -> Type where
      WEmpty : NamesWeakened [<] [<]
      WErased : NamesWeakened ff ff' ->
                NamesWeakened ((:<) ff f @{nprf}) ((:<) ff' Nothing @{NewNothing})
      WEqual : NamesWeakened ff ff' ->
               NamesWeakened ((:<) ff f @{nprf}) ((:<) ff' f @{nprf'})

    public export
    trivialNameWeaken : (ff : UniqNames prs fty) -> NamesWeakened ff ff
    trivialNameWeaken [<] = WEmpty
    trivialNameWeaken (ff :< f) = WEqual (trivialNameWeaken ff)

    public export
    0 newNameInWeakenedPrf : (ff : UniqNames prs fty) ->
                             (ff' : UniqNames prs' fty) ->
                             (f : MaybeP pr fty) ->
                             (0 w : NamesWeakened ff ff') ->
                             (0 nprf : NameIsNew ff f) ->
                             NameIsNew ff' f
    newNameInWeakenedPrf ff ff' Nothing w nprf = NewNothing
    newNameInWeakenedPrf [<] [<] (Just x) WEmpty nprf = EmptyList
    newNameInWeakenedPrf (ff :< Nothing) (ff' :< Nothing) (Just x) (WErased y) (OldNothing z) = OldNothing $ newNameInWeakenedPrf ff ff' (Just x) y z
    newNameInWeakenedPrf (ff :< Just f) (ff' :< Nothing) (Just x) (WErased y) (OldJust _ z) = OldNothing $ newNameInWeakenedPrf ff ff' (Just x) y z
    newNameInWeakenedPrf (ff :< Nothing) (ff' :< Nothing) (Just x) (WEqual y) (OldNothing z) = OldNothing $ newNameInWeakenedPrf ff ff' (Just x) y z
    newNameInWeakenedPrf (ff :< Just f) (ff' :< Just f) (Just x) (WEqual y) (OldJust so z) = OldJust so $ newNameInWeakenedPrf ff ff' (Just x) y z
    newNameInWeakenedPrf (_ :< Nothing) _ (Just _) (WEqual _) (OldJust _ _) impossible
    newNameInWeakenedPrf (_ :< Just _) _ (Just _) (WEqual _) (OldNothing _) impossible

    public export
    data ShallowIndexIn : FsEntries prs mty fty -> Type where
        SHere : ShallowIndexIn $ sx :< Just x
        SThere : ShallowIndexIn sx -> ShallowIndexIn $ sx :< x

    public export
    shallowIndexGet : (sx : FsEntries prs mty fty) ->
                      (sidx : ShallowIndexIn sx) ->
                      FsNode mty fty NotRoot
    shallowIndexGet (xs :< Just x) SHere = x
    shallowIndexGet (xs :< x) (SThere idx) = shallowIndexGet xs idx

    public export
    shallowIndexSet : (sx : FsEntries prs mty fty) ->
                      (names : UniqNames prs fty) ->
                      (sidx : ShallowIndexIn sx) ->
                      (mnode : MaybeP pr' $ FsNode mty fty NotRoot) ->
                      Exists $ \prs' => (FsEntries prs' mty fty, Subset (UniqNames prs' fty) $ \ff' => NamesWeakened names ff')
    shallowIndexSet (sp :< Just p) (ff :< f) SHere Nothing = Evidence _ (sp :< Nothing, Element (ff :< Nothing) $ WErased $ trivialNameWeaken ff)
    shallowIndexSet (sp :< Just p) (ff :< f) SHere (Just x) = Evidence _ (sp :< Just x, Element (ff :< f) $ WEqual $ trivialNameWeaken ff)
    shallowIndexSet (sp :< p) ((:<) ff f @{nprf}) (SThere sidx) mnode with (shallowIndexSet sp ff sidx mnode)
      _ | Evidence prs' (sp', Element ff' wprf') = Evidence _ (sp' :< p, Element ((:<) ff' f @{newNameInWeakenedPrf ff ff' f wprf' nprf}) $ WEqual wprf')

namespace FsNode
    public export
    data IndexIn : {0 mty : RootLabel -> Type} -> FsNode mty fty fs -> RootLabel -> IdxDirLabel -> Type where
        HereFile  : IndexIn (File meta blob) NotRoot FileI 
        HereDir   : IndexIn (Dir meta ns es) NotRoot DirI
        HereRoot  : IndexIn (Root meta ns es) IsRoot DirI
        ThereDir  : IndexIn es dirl -> IndexIn (Dir meta ns es) NotRoot dirl
        ThereRoot : IndexIn es dirl -> IndexIn (Root meta ns es) NotRoot dirl

    public export
    data AtIndex : {node : FsNode mty fty fs} -> (idx : IndexIn node rootl dirl) -> FsNode mty fty fs' -> Type where
        [search node idx]
        HereFile'  : AtIndex {node=File meta blob} HereFile $ File meta blob 
        HereDir'   : AtIndex {node=Dir meta names sx} HereDir $ Dir meta names entries
        HereRoot'  : AtIndex {node=Root meta names sx} HereRoot $ Root meta names entries
        ThereDir'  : AtIndex {sx} i nd -> AtIndex {node = Dir meta names sx} (ThereDir i) nd
        ThereRoot' : AtIndex {sx} i nd -> AtIndex {node = Root meta names sx} (ThereRoot i) nd

    public export
    Uninhabited (FsNode.AtIndex {dirl=FileI} idx (Dir meta names ents)) where
        uninhabited (ThereDir' x) = uninhabited x
        uninhabited (ThereRoot' x) = uninhabited x
    
    public export
    Uninhabited (FsNode.AtIndex {dirl=DirI} idx (File meta blob)) where
        uninhabited (ThereDir' x) = uninhabited x
        uninhabited (ThereRoot' x) = uninhabited x
    
    public export
    indexGet : (node : FsNode mty fty fs) -> (idx : IndexIn node rootl dirl) -> Subset (FsNode mty fty rootl) (\nd => AtIndex idx nd)
    indexGet f@(File {}) HereFile = Element f HereFile'
    indexGet f@(Dir {})  HereDir  = Element f HereDir'
    indexGet f@(Root {}) HereRoot = Element f HereRoot'
    indexGet (Dir _ _ sx) (ThereDir idx) with (indexGet sx idx)
      _ | (Element nd prf) = Element nd $ ThereDir' prf
    indexGet (Root _ _ sx) (ThereRoot idx) with (indexGet sx idx)
      _ | (Element nd prf) = Element nd $ ThereRoot' prf
    

    public export
    indexSet : (node : FsNode mty fty fs) ->
               (idx : IndexIn node rootl dirl) ->
               FsNode mty fty rootl ->
               FsNode mty fty fs
    indexSet nd@(File {}) HereFile f = f
    indexSet nd@(Dir {})  HereDir  f = f
    indexSet nd@(Root {}) HereRoot f = f
    indexSet (Dir meta names sx)  (ThereDir idx)  f = Dir meta names (indexSet sx idx f)
    indexSet (Root meta names sx) (ThereRoot idx) f = Root meta names (indexSet sx idx f)

namespace FsEntries
    data IndexIn : FsEntries prs mty fty -> IdxDirLabel -> Type where
        Here  : IndexIn node NotRoot dirl -> IndexIn {prs = prs :< Present} (nodes :< Just node) dirl
        There : IndexIn sx dirl -> IndexIn (sx :< x) dirl
    
    data AtIndex : {sx : FsEntries prs mty fty} -> (idx : IndexIn sx dirl) -> FsNode mty fty fs' -> Type where
        [search sx idx]
        Here'  : AtIndex {node = x} i nd -> AtIndex {prs = prs :< Present} {sx = sx :< Just x} (Here i) nd
        There' : AtIndex {sx} i nd -> AtIndex {sx = sx :< x} (There i) nd
    
    Uninhabited (FsEntries.AtIndex {dirl = FileI} idx (Dir meta names ents)) where
        uninhabited (Here' x) = uninhabited x
        uninhabited (There' x) = uninhabited x
    
    Uninhabited (FsEntries.AtIndex {dirl = DirI} idx (File meta blob)) where
        uninhabited (Here' x) = uninhabited x
        uninhabited (There' x) = uninhabited x
    
    indexGet (_ :< Just x) (Here idx) with (indexGet x idx)
      _ | (Element nd prf) = Element nd $ Here' prf
    indexGet (xs :< _) (There idx) with (indexGet xs idx)
      _ | (Element nd prf) = Element nd $ There' prf

    indexSet (sx :< Just nd) (Here idx) f = sx :< (Just $ indexSet nd idx f)
    indexSet (sx :< x) (There idx) f = indexSet sx idx f :< x

public export
getAttrsByIndex : (node : FsNode mty fty fs) ->
                  (idx : IndexIn node NotRoot dirl) ->
                  mty NotRoot
getAttrsByIndex node idx with (indexGet node idx)
  _ | (Element (File meta _) _) = meta
  _ | (Element (Dir meta _ _) _) = meta

public export
getBlobByFileIndex : (node : FsNode mty fty fs) ->
                     (idx : IndexIn node NotRoot FileI) ->
                     Exists $ \k => SnocVect k Bits8
getBlobByFileIndex node idx with (indexGet node idx)
    _ | (Element (File _ blob) _) = Evidence _ blob
    _ | (Element (Dir {}) ati) = void $ uninhabited ati

public export
getContentsByDirIndex : (node : FsNode mty fty fs) ->
                        (idx : IndexIn node rootl DirI) ->
                        Exists $ \k => Exists $ \prs => (FsEntries {k} prs mty fty, UniqNames {k} prs fty)
getContentsByDirIndex node idx with (indexGet node idx)
  _ | (Element (File {}) ati) = void $ uninhabited ati
  _ | (Element (Dir _ ff ents) _) = Evidence _ $ Evidence _ (ents, ff)
  _ | (Element (Root _ ff ents) _) = Evidence _ $ Evidence _ (ents, ff)

public export
compoundIndexGet : (node : FsNode mty fty fs) ->
                   (idx : IndexIn node rootl DirI) ->
                   (sidx : ShallowIndexIn $ fst $ snd $ snd $ getContentsByDirIndex node idx) ->
                   FsNode mty fty NotRoot
compoundIndexGet node idx sidx = shallowIndexGet _ sidx
