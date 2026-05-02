module Filesystems.Impl.Posix

import Filesystems.Node
import Filesystems.Node.Index
import Filesystems.NodeOps
import Data.Nat
import Data.DPair
import Data.Vect
import Data.SnocVect
import Data.SnocVect.Quantifiers
import Syntax.IHateParens

%default total
%prefix_record_projections off

public export
interface DefaultFileMeta ty where
    defaultFileMeta : ty

public export
interface DefaultDirMeta ty where
    defaultDirMeta : ty

public export
interface FileWritable ty where
    isWritable : ty -> Bool

public export
newDir : DefaultDirMeta (mty NotRoot) =>
         (node : FsNode mty fty IsRoot) ->
         (idx : IndexIn node rootl DirI) ->
         (name : fty) ->
         (nameprf : NameIsNew (snd $ snd $ snd $ getContentsByDirIndex node idx) (Just name)) ->
         FsNode mty fty IsRoot
newDir node idx name nameprf with (indexGet node idx)
  _ | (Element (Dir meta' names' sx') _) = indexSet node idx (Dir meta' ((:<) names' (Just name) @{nameprf}) (sx' :< Just (Dir defaultDirMeta [<] [<])))
  _ | (Element (Root meta' names' sx') _) = indexSet node idx (Root meta' ((:<) names' (Just name) @{nameprf}) (sx' :< Just (Dir defaultDirMeta [<] [<])))
  _ | (Element (File {}) ati') = void $ uninhabited ati'

public export
newFile : DefaultFileMeta (mty NotRoot) =>
          (node : FsNode mty fty IsRoot) ->
          (idx : IndexIn node rootl DirI) ->
          (name : fty) ->
          (nameprf : NameIsNew (snd $ snd $ snd $ getContentsByDirIndex node idx) (Just name)) ->
          FsNode mty fty IsRoot
newFile node idx name nameprf with (indexGet node idx)
  _ | (Element (Dir meta' names' sx') _) = indexSet node idx (Dir meta' ((:<) names' (Just name) @{nameprf}) (sx' :< Just (File defaultFileMeta [<])))
  _ | (Element (Root meta' names' sx') _) = indexSet node idx (Root meta' ((:<) names' (Just name) @{nameprf}) (sx' :< Just (File defaultFileMeta [<])))
  _ | (Element (File {}) ati') = void $ uninhabited ati'

public export
rmNode : (node : FsNode mty fty IsRoot) ->
         (idx : IndexIn node rootl DirI) ->
         (sidx : ShallowIndexIn $ fst $ snd $ snd $ getContentsByDirIndex node idx) ->
         FsNode mty fty IsRoot
rmNode node idx sidx with (indexGet node idx)
  _ | (Element (File {}) ati) = void $ uninhabited ati
  _ | (Element (Dir meta ff sp) _) with (shallowIndexSet sp ff sidx Nothing)
    _ | (Evidence _ (sp', Element ff' _)) = indexSet node idx (Dir meta ff' sp')
  _ | (Element (Root meta ff sp) _) with (shallowIndexSet sp ff sidx Nothing)
    _ | (Evidence _ (sp', Element ff' _)) = indexSet node idx (Root meta ff' sp')

public export
mvNode : (node : FsNode mty fty IsRoot) ->
         (idx : IndexIn node rootl DirI) ->
         (sidx : ShallowIndexIn $ fst $ snd $ snd $ getContentsByDirIndex node idx) ->
         (idx2 : IndexIn (rmNode node idx sidx) rootl DirI) ->
         (name : fty) ->
         (nameprf : NameIsNew (snd $ snd $ snd $ getContentsByDirIndex (rmNode node idx sidx) idx2) (Just name)) ->
         FsNode mty fty IsRoot
mvNode node idx sidx idx2 name nameprf with (compoundIndexGet _ _ sidx) | (indexGet (rmNode _ _ sidx) idx2)
  _ | _ | Element (File {}) ati = void $ uninhabited ati
  _ | src | Element (Dir meta ff sp) _ = indexSet _ idx2 $ Dir meta .| ff :< Just name .| sp :< Just src
  _ | src | Element (Root meta ff sp) _ = indexSet  _ idx2 $ Root meta .|ff :< Just name .| sp :< Just src

public export
minusLeftSuccLTE : (a : Nat) -> (b : Nat) -> LTE a b -> S (minus b a) = minus (S b) a 
minusLeftSuccLTE 0 0 x = Refl
minusLeftSuccLTE 0 (S k) x = Refl
minusLeftSuccLTE (S k) (S _) (LTESucc x) = minusLeftSuccLTE k _ x

public export
truncate : {n : Nat} -> (def : ty) -> (ssx : SnocVect n ty) -> (off : Nat) -> Vect accl ty -> (SnocVect off ty, Vect (minus n off + accl) ty)
truncate def [<] off acc = (replicate _ def, acc)
truncate {n = n@(S n')} def ssx@(sx :< x) off acc with (isGTE off n)
  _ | (Yes prf) = (replace {p = flip SnocVect ty} (plusCommutative _ _ `trans` plusMinusLte (S n') off prf) $ ssx <>< replicate (minus off $ S n') def, replace {p = flip Vect ty} (cong (+ accl) $ (sym $ minusPlusZero (S n') (minus off $ S n')) `trans` cong (minus $ S n') (plusCommutative (S n') (minus off $ S n') `trans` plusMinusLte _ _ prf)) acc)
  _ | (No contra) = replace {p = \px => (SnocVect off ty, Vect px ty)} ((sym $ plusSuccRightSucc (minus n' off) accl) `trans` cong (+ accl) {a = S $ minus n' off} (minusLeftSuccLTE _ _ $ fromLteSucc $ notLTEImpliesGT contra)) $ truncate def sx off (x :: acc)

public export
overwriteAt : {n : Nat} -> (def : ty) -> (sx : SnocVect n ty) -> (off : Nat) -> {len : Nat} -> (ys : Vect len ty) -> SnocVect (off + len + minus (minus n off) len) ty
overwriteAt def sx off ys with (truncate def sx off [])
  _ | (sv, vs) = rewrite sym $ plusZeroRightNeutral $ minus n off in sv <>< ys <>< drop' vs len where
    drop' : (xs : Vect n' ty) -> (m' : Nat) -> Vect (minus n' m') ty
    drop' [] m' = []
    drop' (n' :: x') 0 = n' :: x'
    drop' (n' :: x') (S k') = drop' x' k'

public export
enrichLen : SnocVect n ty -> (m ** SnocVect m ty)
enrichLen [<] = (0 ** [<])
enrichLen (sx :< x) with (enrichLen sx)
  _ | (m ** sx') = (_ ** sx' :< x)

public export
writeNode : FileWritable (mty NotRoot) =>
            (root : FsNode mty fty IsRoot) ->
            (idx : IndexIn root NotRoot FileI) ->
            (off : Nat) ->
            (len : Nat) ->
            (blob : Vect len Bits8) ->
            FsNode mty fty IsRoot
writeNode root idx off len blob with (indexGet root idx)
  _ | (Element (File meta sx) _) with (enrichLen sx)
    _ | (_ ** sx') = if not $ isWritable meta then root else indexSet _ idx $ File meta $ overwriteAt 0 sx' off blob
  _ | (Element (Dir {}) ati) = void $ uninhabited ati

public export
data PosixOps : FsOpsType mty fty where
    NewDir   : DefaultDirMeta (mty NotRoot) =>
               (idx : IndexIn root rootl DirI) ->
               (name : _) ->
               (nameprf : _) ->
               PosixOps {mty} root $ newDir _ idx name nameprf
    NewFile  : DefaultFileMeta (mty NotRoot) =>
               (idx : IndexIn root rootl DirI) ->
               (name : _) ->
               (nameprf : _) ->
               PosixOps {mty} root $ newFile _ idx name nameprf
    RmNode   : (idx : IndexIn root rootl DirI) ->
               (sidx : _) ->
               PosixOps root $ rmNode _ idx sidx
    MvNode   : (idx : IndexIn root rootl DirI) ->
               (sidx : _) ->
               (idx2 : _) ->
               (name : _) ->
               (nameprf : _) ->
               PosixOps root $ mvNode _ idx sidx idx2 name nameprf
    LsDir    : (idx : IndexIn root rootl DirI) ->
               PosixOps root root
    Read     : (idx : IndexIn root NotRoot FileI) ->
               (src : Nat) ->
               (len : Nat) ->
               (lprf : LTE (src + len) $ fst $ getBlobByFileIndex root idx) ->
               PosixOps root root
    Write    : FileWritable (mty NotRoot) =>
               (idx : IndexIn root NotRoot FileI) ->
               (off : Nat) ->
               (len : Nat) ->
               (blob : Vect len Bits8) ->
               PosixOps {mty} root $ writeNode _ idx off len blob
