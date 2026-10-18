import os
import sys

if os.name == "nt":
    for _flag in ("O_NOFOLLOW", "O_NONBLOCK", "O_DIRECTORY", "O_CLOEXEC"):
        if not hasattr(os, _flag):
            setattr(os, _flag, 0)
    for _stream in (sys.stdout, sys.stderr):
        try:
            _stream.reconfigure(errors="backslashreplace")
        except (AttributeError, ValueError, OSError):
            pass

__all__ = ["__version__"]

__version__ = "0.1.0"
