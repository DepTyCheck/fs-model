module Filesystems.Node

import Data.Vect
import Data.SnocVect
import Data.SnocVect.Quantifiers

%default total
%prefix_record_projections off

public export
data RootLabel = IsRoot | NotRoot

public export
data Presence = Absent | Present

public export
data MaybeP : Presence -> Type -> Type where
    Nothing : MaybeP Absent ty
    Just    : ty -> MaybeP Present ty

namespace UniqNames
    public export
    data UniqNames : SnocVect k Presence -> Type -> Type

    public export
    data NameIsNew : UniqNames prs fty ->
                    MaybeP pr fty ->
                    Type

    data UniqNames : SnocVect k Presence -> Type -> Type where
        Lin : UniqNames [<] fty
        (:<) : (ff : UniqNames prs fty) -> (f : MaybeP pr fty) -> (0 _ : NameIsNew ff f) => UniqNames (prs :< pr) fty

    data NameIsNew : UniqNames prs fty ->
                    MaybeP pr fty ->
                    Type where
        EmptyList : NameIsNew [<] f
        NewNothing : NameIsNew ff Nothing
        OldNothing : (0 sub : NameIsNew ff Nothing) => NameIsNew ff (Just newf) -> NameIsNew ((:<) ff Nothing @{sub}) (Just newf)
        OldJust : Eq fty =>
                  (0 _ : So $ newf /= f) ->
                  {0 ff : UniqNames prs fty} ->
                  NameIsNew {prs} ff (Just newf) ->
                  {0 sub : NameIsNew ff (Just f)} ->
                  NameIsNew {prs=prs :< Present} ((:<) ff (Just f) @{sub}) (Just newf)

public export
data FsNode : (mty : RootLabel -> Type) -> (fty : Type) -> RootLabel -> Type where
    File : (meta : mty NotRoot) ->
           (blob : Vect k Bits8) ->
           FsNode mty fty NotRoot
    Dir  : (meta : mty NotRoot) ->
           (entries : All (flip MaybeP fty) prs) ->
           (names : UniqNames prs fty) ->
           FsNode mty fty NotRoot
    Root : (meta : mty IsRoot) ->
           (entries : All (flip MaybeP fty) prs) ->
           (names : UniqNames prs fty) ->
           FsNode mty fty IsRoot



