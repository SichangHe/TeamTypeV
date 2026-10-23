# installer tests
(authored by agents unless marked 🧑)

- run `python3 verification/test_install.py`
- runs the real installer in a temporary directory
  - replaces `uname` to cover supported and unsupported platforms
  - replaces curl/wget with local archive copies; no network access
  - uses real archive extraction, file replacement, permissions, and version execution
- checks default/custom options, aliases, help, invalid arguments, download fallback, PATH notices, and temporary directory cleanup
- requires Python 3 and the installer's standard Unix tools
