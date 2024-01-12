# SRFI 241 Pattern Matcher

This is my fork of the Marc Nieper-Wißkirchen's implementation of the
[SRFI 241](https://srfi.schemers.org/srfi-241) pattern-matching macro.
I've tried to rewrite the implementation in a simpler and more readable
style, and have made some semantic changes as well.

## Changes from SRFI 241

* The `_` pattern variable is treated as a wildcard. It matches
  anything but is never bound to a value. It can appear any number
  of times in a pattern.

* Only one ellipsis is allowed at each pattern level. SRFI 241 seems to
  allow ambiguous patterns like `(,x ... ,y ... ,z ...)`, which I think
  is a serious bug. It may be possible to support a simple form of
  multi-ellipsis pattern, but it seems best to reject them all, for now.

## License

MIT.
