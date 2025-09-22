# leanblueprint web updates blueprint/lean_decls
default:
	lake build
	leanblueprint web
	lake exe checkdecls blueprint/lean_decls

clean-build:
	lake clean
	lake build
	leanblueprint web
	lake exe checkdecls blueprint/lean_decls
