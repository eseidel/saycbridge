import os.path
PROJECT_DIR = os.path.dirname(__file__) # this is not Django setting.

TEMPLATE_DIRS = (
    os.path.join(PROJECT_DIR, "templates"),
)
