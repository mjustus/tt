module Make (F : Presheaf.S) = struct
  module Base = Context_base.Make (F)
  module Lookup = Context_lookup.Make (F) (Base)

  include Base
  include Lookup
end
