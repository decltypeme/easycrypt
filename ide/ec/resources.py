# --------------------------------------------------------------------
import sys, os

# --------------------------------------------------------------------
class Resource(object):
    ROOT      = os.path.dirname(__file__)
    frozen    = getattr(sys, 'frozen', False)
    easycrypt = 'ec.native'

    @classmethod
    def get(cls, path):
        return os.path.join(cls.ROOT, 'data', *path.split('/'))

    @classmethod
    def rcc(cls, name, compile_=True):
        rccname = cls.get('%srcc.py' % (name,))
        qrcname = cls.get('%s.qrc' % (name,))

        if compile_ and not cls.frozen:
            import subprocess as sp

            if os.path.exists(qrcname):
                try:
                    qmtime = os.path.getmtime(qrcname)
                    rmtime = os.path.getmtime(rccname)
                except OSError:
                    qmtime, rmtime = 1, 0

                if qmtime > rmtime:
                    sp.call(['pyrcc5', '-o', rccname, qrcname])

        return rccname

    @classmethod
    def ui(cls, name):
        return cls.get('%s.ui' % (name,))

    @classmethod
    def html(cls, name):
        return cls.get('web/templates/%s.html' % (name,))

# --------------------------------------------------------------------
if Resource.frozen:
    Resource.ROOT      = os.path.dirname(os.path.realpath(sys.executable))
    Resource.easycrypt = 'easycrypt'