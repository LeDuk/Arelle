# -*- coding: utf-8 -*-
'''
loadFromSDMX.py (initially minimal)
'''
from arelle.Version import authorLabel, copyrightLabel

__pluginInfo__ = {
    'name': 'Load SDMX-ML (User Created)',
    'version': '0.0.1',
    'description': "Handles SDMX 3.0 XML messages (placeholder).",
    'license': 'Apache-2',
    'author': authorLabel,
    'copyright': copyrightLabel,
    # Placeholder, will be properly defined later
    'ModelDocument.IsPullLoadable': None,
    'ModelDocument.PullLoader': None,
}

# Placeholder for Arelle's localization function
def _(message):
    return message

print("arelle.plugin.loadFromSDMX.py minimal file loaded/imported by Arelle")
