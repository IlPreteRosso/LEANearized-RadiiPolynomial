# leanblueprint web updates blueprint/lean_decls
default:
	lake clean
	lake build
	leanblueprint web
	lake exe checkdecls blueprint/lean_decls
