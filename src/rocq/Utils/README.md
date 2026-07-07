This folder contains a variety of files providing necessary utilities that do
not explicitely relate to llvm ir per se.                                                                                
Its content gets re-exported in `/rocq` as a module `Utils` for easier external use.

- `Bool/Option/String/List/Relations-Util.v` generic utilities for the corresponding structures
- `Assoc.v`         utilities for association lists
- `DList.v`         list datastructure for efficient large strings
- `IntMaps.v`       instantiation of the AVL finite maps to [Int]
- `Tactics.v`       generic tactics used across the development
- `ParserHelper.v`  utilities to convert between float representations
