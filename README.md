# SRFI 241 Pattern Matcher

This is my fork of the Marc Nieper-Wißkirchen's implementation of the
[SRFI 241](https://srfi.schemers.org/srfi-241) pattern-matching macro.
I've tried to rewrite the implementation in a simpler and more readable
style, and have made some semantic changes as well.

## Changes from SRFI 241

* The `_` pattern variable is treated as a wildcard. It matches
  anything but is never bound to a value. It can appear any number
  of times in a pattern.

* Only one ellipsis is allowed at each pattern level. `match` accepts
  the same list patterns and vector patterns that are accepted by R7RS
  `syntax-rules`.

## License

MIT.
