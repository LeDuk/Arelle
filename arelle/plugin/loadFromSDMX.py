# -*- coding: utf-8 -*-
"""
loadFromSDMX.py is an Arelle plugin that supports loading SDMX-CSV facts into an DTS, 
either as new instances or by merging into existing instances.

(c) Copyright 2016-2022 Mark V Systems Limited, All rights reserved.
Mark V Systems Limited is a Full Member of XBRL International.
This software is distributed under the terms of the Apache License, Version 2.0.
Please see the License for the specific language governing permissions and
limitations under the License.

References:

  SDMX-CSV: https://sdmx.org/wp-content/uploads/SDMX_2_1_SECTION_7_CSV_201303.pdf
  Guidelines for the use of SDMX-CSV: https://sdmx.org/wp-content/uploads/SDMX_CSV_Guidelines_201403.pdf
  DRAFT SDMX-CSV 2.0: https://github.com/sdmx-twg/sdmx-csv/blob/master/specification/sdmx-csv-specification.md

Transformations:

  For DSDs describing XBRL taxonomies, dimensions in the DSD are mapped to dimensions in an XBRL taxonomy.
  The DSD describes series of observations, each series having a common set of dimension values and varying observation values.
  Each series has a different set of dimension values.
  
  Primary measures (OBS_VALUE in SDMX-CSV, which are observations) become facts.
  Attributes that are observation-specific (attached to OBS_VALUE) become attributes on those facts.
  Attributes that are series-specific (attached to a series of observations) become attributes on those facts.
  Attributes that are group-specific (attached to a group of series) become attributes on those facts.
  Attributes that are dataset-specific (attached to the dataset) become attributes on those facts.

  SDMX dimensions are mapped to XBRL dimensions by an XBRL taxonomy data structure, a tuple:
     (dimension concept, domain concept, member concept, isTyped, sdmxName)
  The sdmxName is the SDMX dimension name.
  If isTyped is True, the dimension value is the text of the dimension value.
  If isTyped is False, the dimension value is mapped to a member concept by an XBRL taxonomy data structure, a tuple:
     (dimension concept, domain concept, member concept, sdmxValue)
  The sdmxValue is the SDMX dimension value.

  The XBRL taxonomy data structure is loaded from a JSON file, the "sdmx-xbrl-map.json" file.
  The map file defines mappings for a specific DSD.
  The map file has these entries:
    "dsd": "dsd file name or url"
    "namespace": "target namespace for concepts"
    "concepts": { sdmxName: conceptName ... }
    "dimensions": [ (dimension concept, domain concept, member concept, isTyped, sdmxName) ... ]
    "members": [ (dimension concept, domain concept, member concept, sdmxValue) ... ]
    "measures": [ (measure concept, sdmxName) ... ]
    "attributes": [ (attribute concept, sdmxName) ... ]
    "units": { sdmxName: unitId ... }
    "languages": { sdmxName: lang ... }

"""

import os, io, json, csv, datetime, re, traceback
from lxml import etree
from collections import defaultdict, OrderedDict
from arelle import ModelDocument, XmlUtil, XbrlConst, ModelXbrl, ModelInstanceObject
from arelle.ModelValue import qname, QName, dateTime, DATETIME, DATEUNION, dateunionDate, yearMonthDuration, dayTimeDuration
from arelle.PrototypeDts import LocPrototype, ArcPrototype
from arelle.PythonUtil import OrderedDefaultDict
from arelle.UrlUtil import isAbsolute
from arelle.ValidateXbrlDimensions import isFactDimensionallyValid
from arelle.XmlValidate import VALID

nsPattern = re.compile(r"{([^}]*)}")
attrPattern = re.compile(r"([a-zA-Z0-9_]+):([a-zA-Z0-9_]+)")

CSV_DSF_firstRow = "dataflow,keyFamily,datastructureID" # specific to ECB's DSF
CSV_seriesKeyFirstCol = "FREQ" # first column of series keys

# Global variables to cache the last checked filepath and its SDMX status
lastFilePath = None
lastFilePathIsSDMX = False

def isSdmxLoadable(modelXbrl, mappedUri, normalizedUri, filepath, **kwargs):
    global lastFilePath, lastFilePathIsSDMX
    lastFilePath = filepath
    lastFilePathIsSDMX = False

    _ext = os.path.splitext(filepath)[1]
    if not _ext.lower() == ".xml":
        return False

    try:
        with modelXbrl.fileSource.file(filepath, 'rb') as fh:
            # Use iterparse to read only the root element
            for event, element in etree.iterparse(fh, events=("start",), recover=True, huge_tree=True):
                if event == "start":
                    root_tag = element.tag
                    # Check for SDMX namespaces (version 3.0 or 2.1)
                    if root_tag.startswith("{http://www.sdmx.org/resources/sdmxml/schemas/v3_0/") or \
                       root_tag.startswith("{http://www.sdmx.org/resources/sdmxml/schemas/v2_1/"):
                        # Optionally, check local name for common SDMX root elements
                        # local_name = etree.QName(root_tag).localname
                        # sdmx_root_elements = {"Structure", "GenericData", "StructureSpecificData", 
                        #                       "RegistryInterface", "Error", "GenericMetadata", 
                        #                       "StructureSpecificMetadata"} # Add more if needed
                        # if local_name in sdmx_root_elements:
                        #     lastFilePathIsSDMX = True
                        #     return True
                        # For now, matching the namespace is sufficient
                        lastFilePathIsSDMX = True
                        return True
                    else:
                        # Root element is not in a recognized SDMX namespace
                        return False 
                break # Only process the first element (root)
    except etree.LxmlError as err:
        modelXbrl.error("isSdmxLoadable:lxmlError",
                        "LXML error while sniffing file %(file)s: %(error)s",
                        modelObject=modelXbrl, file=filepath, error=str(err))
        return False
    except IOError as err:
        modelXbrl.error("isSdmxLoadable:ioError",
                        "IO error while sniffing file %(file)s: %(error)s",
                        modelObject=modelXbrl, file=filepath, error=str(err))
        return False
    except Exception as err:
        modelXbrl.error("isSdmxLoadable:generalError",
                        "Unexpected error while sniffing file %(file)s: %(error)s",
                        modelObject=modelXbrl, file=filepath, error=str(err))
        return False
        
    return False # Default if no SDMX root found or other issue

def sdmxLoader(modelXbrl, mappedUri, filepath, *args, **kwargs):
    '''
    Entry point for Arelle to load an SDMX file.
    '''
    global lastFilePath, lastFilePathIsSDMX # ensure we're using the globals

    # If isSdmxLoadable was called and confirmed it, lastFilePathIsSDMX would be True
    # and lastFilePath would match filepath.
    # If not, or if called directly, we might need to re-evaluate.
    if filepath != lastFilePath: # File changed since last isSdmxLoadable check
        isSdmxLoadable(modelXbrl, mappedUri, None, filepath) # Run the check now, it will update globals

    if not lastFilePathIsSDMX: # If still not confirmed as SDMX by isSdmxLoadable
        return None # Not an SDMX file

    # Proceed with loading as it's confirmed (or re-confirmed) to be SDMX
    cntlr = modelXbrl.modelManager.cntlr
    
    # Call the actual loading function (renamed from the original loadFromSdmx)
    # Note: sdmxDoc is expected by _actual_loadFromSdmx but not directly available here.
    # _actual_loadFromSdmx will need to read the file itself if sdmxDoc is None.
    # sdmxUrl can be mappedUri or filepath.
    return _actual_loadFromSdmx(cntlr, cntlr.addToLog, cntlr.addToLog, modelXbrl, filepath, mappedUri, sdmxDoc=None)

def _actual_loadFromSdmx(cntlr, error, warning, modelXbrl, sdmxFile, sdmxUrl, sdmxDoc=None):
    # check if an existing document is a generic instance
    missing = []
    if modelXbrl.modelDocument is None:
        missing.append(_("No model document exists for instance"))
    elif modelXbrl.modelDocument.type not in (ModelDocument.Type.INSTANCE, ModelDocument.Type.INLINEXBRL):
        missing.append(_("Existing document is not an instance or inline XBRL document"))
    
    # Initialize default unit
    uPure = None
    created_units = {}
    try:
        # Try to use XbrlConst if available and qname is properly defined
        if XbrlConst and hasattr(XbrlConst, 'qnXbrliPure') and XbrlConst.qnXbrliPure:
            uPure = modelXbrl.createUnit([XbrlConst.qnXbrliPure], [])
        else: # Fallback if XbrlConst.qnXbrliPure is not available or not a QName
            uPure = modelXbrl.createUnit([qname("http://www.xbrl.org/2003/instance", "pure")], [])
        if uPure is not None:
            created_units['pure'] = uPure
        else:
            missing.append("Failed to create default 'pure' unit.")
            # No error call here, as it might be recoverable if units are defined in SDMX or map
    except Exception as e:
        missing.append(f"Exception creating default 'pure' unit: {e}")
        # Log as warning for now, as CSV part might not need it or it might be defined later
        warning("arelle:loadFromSdmxUnitError", f"Exception creating default 'pure' unit: {e}")

    if missing and not _sdmxType == "XML": # For XML, header parsing might resolve this or make it critical later
         error("arelle:loadFromSdmxMissingPrerequisite", "; ".join(missing))
         return None


    if sdmxDoc is None: # called from GUI
        # load sdmx file
        if not os.path.isabs(sdmxFile):
            sdmxFile = os.path.join(os.path.dirname(modelXbrl.modelDocument.filepath), sdmxFile)
        if not os.path.exists(sdmxFile):
            error("arelle:loadFromSdmxFileNotFound",
                  _("SDMX file not found: %(sdmxFile)s"),
                  sdmxFile=sdmxFile)
            return None
        try:
            with io.open(sdmxFile, 'rt', encoding='utf-8-sig') as fh: # remove BOM if present
                sdmxDoc = fh.read()
        except Exception as ex:
            error("arelle:loadFromSdmxFileNotReadable",
                  _("Error reading SDMX file: %(sdmxFile)s, error: %(error)s"),
                  sdmxFile=sdmxFile, error=ex)
            return None

    # parse sdmx file
    # determine if SDMX-CSV or SDMX-XML
    if sdmxDoc.startswith("dataflow,keyFamily,datastructureID") or sdmxDoc.startswith('"dataflow","keyFamily","datastructureID"'): # DSF
        # special case for ECB data structure file
        # first line is dataflow,keyFamily,datastructureID
        # subsequent lines are DSD specific dimension names
        # last line is OBS_VALUE
        # from this construct a standard SDMX-CSV file
        missing.append("ECB Data Structure File (DSF) is not yet supported.")
    elif '<' not in sdmxDoc: # SDMX-CSV (guess)
        # assume SDMX-CSV
        # find DSD for this CSV file
        # if path is relative, it is relative to CSV file
        _sdmxType = "CSV"
        # TBD: find DSD for this CSV file
        dsdUrl = None # for now, assume map file names the dsd
        # if path is relative, it is relative to CSV file
        # for now assume map file has dsd url
    elif sdmxDoc.startswith("<?xml") or sdmxDoc.startswith("<"): # SDMX-XML (guess)
        _sdmxType = "XML"
        # find DSD for this XML file
        # missing.append("SDMX-ML is not yet supported.") # Removed placeholder

        try:
            # Ensure sdmxDoc has content
            if not isinstance(sdmxDoc, str) or not sdmxDoc:
                if sdmxFile:
                    try:
                        # Attempt to read sdmxFile content into sdmxDoc
                        with io.open(sdmxFile, 'rt', encoding='utf-8-sig') as fh:
                            sdmxDoc = fh.read()
                        if not sdmxDoc: # Check if file was empty
                            missing.append(f"SDMX file is empty: {sdmxFile}")
                            error("arelle:loadFromSdmxFileEmpty", "SDMX file is empty: %(sdmxFile)s", sdmxFile=sdmxFile)
                    except IOError as e:
                        missing.append(f"IOError reading SDMX file {sdmxFile}: {e}")
                        error("arelle:loadFromSdmxFileNotFound", "Error reading SDMX file: %(sdmxFile)s, error: %(error)s", sdmxFile=sdmxFile, error=e)
                        sdmxDoc = None # Ensure sdmxDoc is None if read failed
                else: # No sdmxFile provided and sdmxDoc is empty
                    missing.append("SDMX document content is not available.")
                    error("arelle:loadFromSdmxNoContent", "SDMX document content is not available.")
                    sdmxDoc = None

            if sdmxDoc: # Proceed only if sdmxDoc has content
                # Parse XML String
                try:
                    xml_root = etree.fromstring(sdmxDoc.encode('utf-8'))
                except etree.LxmlError as e:
                    missing.append(f"XML parsing error: {e}")
                    error("arelle:loadFromSdmxXmlError", "XML parsing error in %(sdmxFile)s: %(error)s", sdmxFile=sdmxFile, error=e)
                    xml_root = None # Ensure xml_root is None if parsing failed

                if xml_root is not None:
                    # Define Namespaces
                    ns = {
                        'm': 'http://www.sdmx.org/resources/sdmxml/schemas/v3_0/message',
                        'cmn': 'http://www.sdmx.org/resources/sdmxml/schemas/v3_0/common',
                        'str': 'http://www.sdmx.org/resources/sdmxml/schemas/v3_0/structure'
                    }
                    # Also consider v2.1 namespaces if needed, or make ns dynamic based on detected root ns
                    ns_v21 = {
                        'm': 'http://www.sdmx.org/resources/sdmxml/schemas/v2_1/message',
                        'str': 'http://www.sdmx.org/resources/sdmxml/schemas/v2_1/structure',
                        'data': 'http://www.sdmx.org/resources/sdmxml/schemas/v2_1/data',
                        'cmn': 'http://www.sdmx.org/resources/sdmxml/schemas/v2_1/common'
                    }


                    # Validate Root Element
                    qname_root = etree.QName(xml_root.tag)
                    msg_localname = qname_root.localname
                    msg_namespace = qname_root.namespace

                    if not (msg_namespace.startswith("http://www.sdmx.org/resources/sdmxml/schemas/v3_0/") or \
                            msg_namespace.startswith("http://www.sdmx.org/resources/sdmxml/schemas/v2_1/")):
                        missing.append(f"Invalid SDMX root element namespace: {msg_namespace}")
                        error("arelle:loadFromSdmxXmlError", "Invalid SDMX root element namespace: %(namespace)s in %(sdmxFile)s", namespace=msg_namespace, sdmxFile=sdmxFile)
                    elif msg_localname not in {"Structure", "GenericData", "StructureSpecificData", "RegistryInterface", "Error", "GenericMetadata", "StructureSpecificMetadata"}:
                        missing.append(f"Invalid SDMX root element local name: {msg_localname}")
                        error("arelle:loadFromSdmxXmlError", "Invalid SDMX root element local name: %(localname)s in %(sdmxFile)s", localname=msg_localname, sdmxFile=sdmxFile)
                    else:
                        cntlr.addToLog(f"SDMX-ML message type: {msg_localname} (Namespace: {msg_namespace})")
                        
                        # Adjust ns map if v2.1 detected
                        if msg_namespace.startswith("http://www.sdmx.org/resources/sdmxml/schemas/v2_1/"):
                            ns = ns_v21

                        # Parse Header
                        header_el = xml_root.find('m:Header', namespaces=ns)
                        if header_el is None:
                            missing.append("SDMX Header not found.")
                            error("arelle:loadFromSdmxXmlError", "SDMX Header (m:Header) not found in %(sdmxFile)s", sdmxFile=sdmxFile)
                        else:
                            header_id_el = header_el.find('m:ID', namespaces=ns)
                            if header_id_el is not None:
                                cntlr.addToLog(f"Header ID: {header_id_el.text}")
                            
                            header_test_el = header_el.find('m:Test', namespaces=ns)
                            if header_test_el is not None:
                                cntlr.addToLog(f"Header Test: {header_test_el.text}")

                            header_prepared_el = header_el.find('m:Prepared', namespaces=ns)
                            if header_prepared_el is not None:
                                cntlr.addToLog(f"Header Prepared: {header_prepared_el.text}")

                            sender_el = header_el.find('m:Sender', namespaces=ns)
                            if sender_el is not None:
                                cntlr.addToLog(f"Header Sender ID: {sender_el.get('id')}")
                            
                            # Extract DSD References
                            dsd_references_log = []
                            for struct_el in header_el.findall('m:Structure', namespaces=ns):
                                structure_id_attr = struct_el.get('structureID')
                                current_dsd_ref_str = f"Header m:Structure (structureID={structure_id_attr or 'None'}) "
                                
                                dsd_defining_container = None
                                ref_detail_type = ""

                                prov_agree_el = struct_el.find('cmn:ProvisionAgreement', namespaces=ns)
                                if prov_agree_el is not None:
                                    dsd_defining_container = prov_agree_el
                                    ref_detail_type = "cmn:ProvisionAgreement"
                                else:
                                    struct_usage_el = struct_el.find('cmn:StructureUsage', namespaces=ns)
                                    if struct_usage_el is not None:
                                        dsd_defining_container = struct_usage_el
                                        ref_detail_type = "cmn:StructureUsage"
                                    else:
                                        # SDMX 3.0 uses cmn:Structure directly inside m:Structure for DSD reference
                                        # SDMX 2.1 uses str:Structure or similar directly for DSD reference (not cmn:Structure)
                                        # For SDMX 3.0 style:
                                        direct_struct_ref_el = struct_el.find('cmn:Structure', namespaces=ns)
                                        if direct_struct_ref_el is not None:
                                            dsd_defining_container = direct_struct_ref_el
                                            ref_detail_type = "cmn:Structure"
                                        # For SDMX 2.1 style (example, may need refinement based on actual 2.1 structure)
                                        elif msg_namespace.startswith("http://www.sdmx.org/resources/sdmxml/schemas/v2_1/"):
                                            # In 2.1, m:Structure might directly contain str:DataStructure, str:ConceptScheme etc.
                                            # or a Ref to it. The DSD itself is a str:DataStructure.
                                            # For simplicity, we'll look for a Ref as that's common.
                                            # This part might need more specific handling for 2.1 DSD references.
                                            pass # Placeholder for more specific 2.1 handling if needed beyond Ref

                                if dsd_defining_container is not None:
                                    urn_el = dsd_defining_container.find('cmn:URN', namespaces=ns)
                                    if urn_el is not None:
                                        current_dsd_ref_str += f"references DSD via {ref_detail_type} URN: {urn_el.text}"
                                    else:
                                        ref_el = dsd_defining_container.find('cmn:Ref', namespaces=ns)
                                        if ref_el is not None:
                                            ref_id = ref_el.get('id')
                                            ref_agency = ref_el.get('agencyID')
                                            ref_version = ref_el.get('version')
                                            current_dsd_ref_str += (f"references DSD via {ref_detail_type} cmn:Ref (ID={ref_id}, "
                                                                    f"Agency={ref_agency}, Version={ref_version})")
                                        else:
                                            current_dsd_ref_str += f"contains {ref_detail_type} but no cmn:URN or cmn:Ref child."
                                else:
                                    current_dsd_ref_str += ("has no cmn:ProvisionAgreement, cmn:StructureUsage, or direct cmn:Structure "
                                                            "container for DSD reference details.")
                                
                                dsd_references_log.append(current_dsd_ref_str)
                                cntlr.addToLog(current_dsd_ref_str)

                            # Log summary message
                            if msg_localname == "Structure":
                                # cntlr.addToLog("SDMX Structure message identified. This message may define DSDs or other structural metadata.") # Old message
                                structures_element = xml_root.find('str:Structures', namespaces=ns)
                                if structures_element is None:
                                    error("arelle:loadFromSdmxXmlError",
                                          "No <str:Structures> element found in Structure message in file %(file)s.",
                                          modelObject=modelXbrl, file=sdmxFile)
                                    missing.append(f"No <str:Structures> element found in Structure message in {sdmxFile}.")
                                else:
                                    cntlr.addToLog("Found <str:Structures> element. Parsing structural metadata.", messageCode="loadFromSdmx:info")
                                    if not hasattr(modelXbrl, 'sdmxStructures'):
                                        modelXbrl.sdmxStructures = {
                                            "concept_schemes": {}, # Store by URN or (agency, id, version)
                                            "codelists": {},       # Store by URN or (agency, id, version)
                                            "dsds": {}             # Store by URN or (agency, id, version)
                                        }
                                    
                                    # Parse ConceptSchemes
                                    for cs_el in structures_element.findall('str:ConceptScheme', namespaces=ns):
                                        cs_id = cs_el.get('id')
                                        cs_agency = cs_el.get('agencyID')
                                        cs_version = cs_el.get('version')
                                        cs_urn = cs_el.get('urn')
                                        # Determine a unique key for storing the concept scheme
                                        cs_key = cs_urn if cs_urn else (cs_agency, cs_id, cs_version)
                                        
                                        parsed_cs = {'id': cs_id, 'agencyID': cs_agency, 'version': cs_version, 'urn': cs_urn, 'concepts': {}}
                                        cntlr.addToLog(f"Parsing ConceptScheme: id={cs_id}, agency={cs_agency}, version={cs_version}, urn={cs_urn}", messageCode="loadFromSdmx:info")
                                        
                                        for concept_el in cs_el.findall('str:Concept', namespaces=ns):
                                            concept_id = concept_el.get('id')
                                            concept_urn = concept_el.get('urn') # Optional URN for the concept itself
                                            parsed_concept = {'id': concept_id, 'urn': concept_urn, 'names': {}}
                                            for name_el in concept_el.findall('cmn:Name', namespaces=ns):
                                                lang = name_el.get('{http://www.w3.org/XML/1998/namespace}lang', 'en')
                                                parsed_concept['names'][lang] = name_el.text
                                            # Store concept by its ID within the scheme
                                            parsed_cs['concepts'][concept_id] = parsed_concept 
                                        
                                        modelXbrl.sdmxStructures["concept_schemes"][cs_key] = parsed_cs
                                        cntlr.addToLog(f"Stored ConceptScheme: {cs_key} with {len(parsed_cs['concepts'])} concepts.", messageCode="loadFromSdmx:info")

                                    # Parse Codelists
                                    for cl_el in structures_element.findall('str:Codelist', namespaces=ns):
                                        cl_id = cl_el.get('id')
                                        cl_agency = cl_el.get('agencyID')
                                        cl_version = cl_el.get('version')
                                        cl_urn = cl_el.get('urn')
                                        cl_key = cl_urn if cl_urn else (cl_agency, cl_id, cl_version)

                                        parsed_cl = {'id': cl_id, 'agencyID': cl_agency, 'version': cl_version, 'urn': cl_urn, 'codes': {}}
                                        cntlr.addToLog(f"Parsing Codelist: id={cl_id}, agency={cl_agency}, version={cl_version}, urn={cl_urn}", messageCode="loadFromSdmx:info")

                                        for code_el in cl_el.findall('str:Code', namespaces=ns):
                                            code_id = code_el.get('id')
                                            code_urn = code_el.get('urn') # Optional URN for the code itself
                                            parsed_code = {'id': code_id, 'urn': code_urn, 'names': {}}
                                            for name_el in code_el.findall('cmn:Name', namespaces=ns):
                                                lang = name_el.get('{http://www.w3.org/XML/1998/namespace}lang', 'en')
                                                parsed_code['names'][lang] = name_el.text
                                            parsed_cl['codes'][code_id] = parsed_code
                                        
                                        modelXbrl.sdmxStructures["codelists"][cl_key] = parsed_cl
                                        cntlr.addToLog(f"Stored Codelist: {cl_key} with {len(parsed_cl['codes'])} codes.", messageCode="loadFromSdmx:info")

                                    # Parse DataStructures (DSDs)
                                    for dsd_el in structures_element.findall('str:DataStructure', namespaces=ns):
                                        dsd_id = dsd_el.get('id')
                                        dsd_agency = dsd_el.get('agencyID')
                                        dsd_version = dsd_el.get('version')
                                        dsd_urn = dsd_el.get('urn')
                                        dsd_key = dsd_urn if dsd_urn else (dsd_agency, dsd_id, dsd_version)

                                        parsed_dsd = {
                                            'id': dsd_id, 'agencyID': dsd_agency, 'version': dsd_version, 'urn': dsd_urn,
                                            'dimensions': OrderedDict(), # Preserve order for key construction
                                            'time_dimension': None,
                                            'attributes': {},
                                            'measures': {}
                                        }
                                        cntlr.addToLog(f"Parsing DataStructure (DSD): id={dsd_id}, agency={dsd_agency}, version={dsd_version}, urn={dsd_urn}", messageCode="loadFromSdmx:info")

                                        # DimensionList
                                        dim_list_el = dsd_el.find('str:DimensionList', namespaces=ns)
                                        if dim_list_el is not None:
                                            for dim_el in dim_list_el.findall('str:Dimension', namespaces=ns):
                                                dim_id = dim_el.get('id')
                                                concept_identity_el = dim_el.find('str:ConceptIdentity/cmn:Ref', namespaces=ns) # Assuming Ref for now
                                                concept_ref = None
                                                if concept_identity_el is not None:
                                                    concept_ref = {
                                                        'id': concept_identity_el.get('id'),
                                                        'agencyID': concept_identity_el.get('agencyID'),
                                                        'version': concept_identity_el.get('version'),
                                                        'maintainableParentID': concept_identity_el.get('maintainableParentID') # ConceptScheme ID
                                                    }
                                                
                                                local_rep_el = dim_el.find('str:LocalRepresentation', namespaces=ns)
                                                representation = None
                                                if local_rep_el is not None:
                                                    enum_el = local_rep_el.find('cmn:Enumeration/cmn:Ref', namespaces=ns) # Assuming Ref for Codelist
                                                    if enum_el is not None:
                                                        representation = {'type': 'codelist', 'ref': {
                                                            'id': enum_el.get('id'), 'agencyID': enum_el.get('agencyID'),
                                                            'version': enum_el.get('version')
                                                        }}
                                                    else:
                                                        text_format_el = local_rep_el.find('cmn:TextFormat', namespaces=ns)
                                                        if text_format_el is not None:
                                                            representation = {'type': 'textFormat', 
                                                                              'textType': text_format_el.get('textType'),
                                                                              'dataType': text_format_el.get('dataType')} # SDMX 2.1 uses dataType
                                                
                                                parsed_dsd['dimensions'][dim_id] = {'id': dim_id, 'concept_ref': concept_ref, 'representation': representation}

                                            time_dim_el = dim_list_el.find('str:TimeDimension', namespaces=ns)
                                            if time_dim_el is not None:
                                                time_dim_id = time_dim_el.get('id') # Usually fixed to TIME_PERIOD
                                                concept_identity_el = time_dim_el.find('str:ConceptIdentity/cmn:Ref', namespaces=ns)
                                                concept_ref = None
                                                if concept_identity_el is not None:
                                                    concept_ref = {
                                                        'id': concept_identity_el.get('id'), 'agencyID': concept_identity_el.get('agencyID'),
                                                        'version': concept_identity_el.get('version'),
                                                        'maintainableParentID': concept_identity_el.get('maintainableParentID')
                                                    }
                                                # TimeDimension has a specific representation (TimeDimensionRepresentationType)
                                                # For now, just note its presence and concept. Detailed parsing of its TextFormat can be added if needed.
                                                parsed_dsd['time_dimension'] = {'id': time_dim_id, 'concept_ref': concept_ref}
                                        
                                        # AttributeList
                                        attr_list_el = dsd_el.find('str:AttributeList', namespaces=ns)
                                        if attr_list_el is not None:
                                            for attr_el in attr_list_el.findall('str:Attribute', namespaces=ns):
                                                attr_id = attr_el.get('id')
                                                concept_identity_el = attr_el.find('str:ConceptIdentity/cmn:Ref', namespaces=ns)
                                                concept_ref = None
                                                if concept_identity_el is not None:
                                                    concept_ref = {
                                                        'id': concept_identity_el.get('id'), 'agencyID': concept_identity_el.get('agencyID'),
                                                        'version': concept_identity_el.get('version'),
                                                        'maintainableParentID': concept_identity_el.get('maintainableParentID')
                                                    }
                                                
                                                local_rep_el = attr_el.find('str:LocalRepresentation', namespaces=ns)
                                                representation = None # Similar parsing as for Dimension
                                                if local_rep_el is not None: # Simplified for brevity
                                                    enum_el = local_rep_el.find('cmn:Enumeration/cmn:Ref', namespaces=ns)
                                                    if enum_el is not None: representation = {'type': 'codelist', 'ref_id': enum_el.get('id')} # store enough to find codelist
                                                    else: 
                                                        tf_el = local_rep_el.find('cmn:TextFormat', namespaces=ns)
                                                        if tf_el is not None: representation = {'type': 'textFormat', 'textType': tf_el.get('textType')}


                                                # AttributeRelationship (important for data parsing)
                                                attr_rel_el = attr_el.find('str:AttributeRelationship', namespaces=ns)
                                                relationship = "DataSet" # Default if not specified or more complex
                                                if attr_rel_el is not None:
                                                    if attr_rel_el.find('str:None', namespaces=ns) is not None: relationship = "None" # No specific attachment (DataSet/Observation by default based on usage)
                                                    elif attr_rel_el.find('str:PrimaryMeasure', namespaces=ns) is not None: relationship = "PrimaryMeasure"
                                                    elif attr_rel_el.findall('str:Dimension', namespaces=ns): # list of dimension refs
                                                        relationship = [d.get('id') for d in attr_rel_el.findall('str:Dimension', namespaces=ns)]
                                                    elif attr_rel_el.find('str:Group', namespaces=ns) is not None:
                                                        relationship = {"groupRef": attr_rel_el.find('str:Group', namespaces=ns).get('id')} # simplified
                                                    # In SDMX 3.0, AttributeRelationship is more complex with choices like <str:Observation>, <str:Dataflow>
                                                    # This simplified parsing captures some common cases.
                                                    # A more robust implementation would parse the full choice.
                                                    # For now, if any specific child is found, we'll just note the first one.
                                                    first_rel_child = next(iter(attr_rel_el), None)
                                                    if first_rel_child is not None:
                                                        relationship = etree.QName(first_rel_child.tag).localname


                                                usage_status = attr_el.get('usage', 'optional')
                                                parsed_dsd['attributes'][attr_id] = {'id': attr_id, 'concept_ref': concept_ref, 
                                                                                     'representation': representation, 
                                                                                     'relationship': relationship, 'usage': usage_status}

                                        # MeasureList (PrimaryMeasure)
                                        measure_list_el = dsd_el.find('str:MeasureList', namespaces=ns)
                                        if measure_list_el is not None:
                                            # Typically one primary measure, e.g. OBS_VALUE
                                            for measure_el in measure_list_el.findall('str:Measure', namespaces=ns):
                                                measure_id = measure_el.get('id') # This is the PrimaryMeasure (e.g. OBS_VALUE)
                                                concept_identity_el = measure_el.find('str:ConceptIdentity/cmn:Ref', namespaces=ns)
                                                concept_ref = None
                                                if concept_identity_el is not None:
                                                    concept_ref = {
                                                        'id': concept_identity_el.get('id'), 'agencyID': concept_identity_el.get('agencyID'),
                                                        'version': concept_identity_el.get('version'),
                                                        'maintainableParentID': concept_identity_el.get('maintainableParentID')
                                                    }
                                                # Representation for measure (usually a number type)
                                                local_rep_el = measure_el.find('str:LocalRepresentation/cmn:TextFormat', namespaces=ns)
                                                representation = None
                                                if local_rep_el is not None:
                                                    representation = {'type': 'textFormat', 'textType': local_rep_el.get('textType')}
                                                
                                                parsed_dsd['measures'][measure_id] = {'id': measure_id, 'concept_ref': concept_ref, 'representation': representation}
                                        
                                        modelXbrl.sdmxStructures["dsds"][dsd_key] = parsed_dsd
                                        cntlr.addToLog(f"Stored DSD: {dsd_key} with {len(parsed_dsd['dimensions'])} dimensions, {len(parsed_dsd['attributes'])} attributes, {len(parsed_dsd['measures'])} measures.", messageCode="loadFromSdmx:info")
                                    # Placeholder for parsing other structural metadata like DSDs
                                    missing.append("SDMX-ML Structure message: Further structural metadata (e.g., Dataflows, MetadataStructureDefinitions) parsing not yet implemented.")
                            
                            elif msg_localname in {"GenericData", "StructureSpecificData"}: # Data message
                                active_dsd_key = None
                                retrieved_dsd = None
                                dsd_lookup_status_message = ""

                                first_header_structure_el = header_el.find('m:Structure', namespaces=ns)
                                if first_header_structure_el:
                                    dsd_defining_container = None
                                    pa_el = first_header_structure_el.find('cmn:ProvisionAgreement', namespaces=ns)
                                    if pa_el is not None: dsd_defining_container = pa_el
                                    else:
                                        su_el = first_header_structure_el.find('cmn:StructureUsage', namespaces=ns)
                                        if su_el is not None: dsd_defining_container = su_el
                                        else:
                                            s_el = first_header_structure_el.find('cmn:Structure', namespaces=ns)
                                            if s_el is not None: dsd_defining_container = s_el
                                    
                                    if dsd_defining_container:
                                        urn_el = dsd_defining_container.find('cmn:URN', namespaces=ns)
                                        if urn_el is not None:
                                            active_dsd_key = urn_el.text
                                        else:
                                            ref_el = dsd_defining_container.find('cmn:Ref', namespaces=ns)
                                            if ref_el is not None:
                                                active_dsd_key = (ref_el.get('agencyID'), ref_el.get('id'), ref_el.get('version'))
                                
                                if active_dsd_key:
                                    if hasattr(modelXbrl, 'sdmxStructures') and "dsds" in modelXbrl.sdmxStructures:
                                        retrieved_dsd = modelXbrl.sdmxStructures["dsds"].get(active_dsd_key)
                                        if retrieved_dsd:
                                            dsd_lookup_status_message = f"For data message {msg_localname}, successfully retrieved DSD: {active_dsd_key}"
                                            cntlr.addToLog(dsd_lookup_status_message, messageCode="loadFromSdmx:info")
                                            modelXbrl.currentSdmxActiveDsd = retrieved_dsd # Store for later use
                                        else:
                                            dsd_lookup_status_message = f"For data message {msg_localname}, DSD NOT FOUND for key: {active_dsd_key}. Data parsing cannot proceed without DSD."
                                            cntlr.addToLog(dsd_lookup_status_message, messageCode="loadFromSdmx:error")
                                            if msg_localname == "StructureSpecificData": # Critical for StructureSpecificData
                                                error("arelle:loadFromSdmxMissingDSDForData", dsd_lookup_status_message)
                                    else:
                                        dsd_lookup_status_message = f"For data message {msg_localname}, sdmxStructures dictionary not found. Was a Structure message loaded?"
                                        cntlr.addToLog(dsd_lookup_status_message, messageCode="loadFromSdmx:error")
                                        if msg_localname == "StructureSpecificData":
                                             error("arelle:loadFromSdmxMissingDSDForData", dsd_lookup_status_message)
                                else: # No DSD reference found in the header for this data message
                                    dsd_lookup_status_message = f"For data message {msg_localname}, no DSD reference found in header. This may be an issue for StructureSpecificData."
                                    cntlr.addToLog(dsd_lookup_status_message, messageCode="loadFromSdmx:warning")
                                    if msg_localname == "StructureSpecificData":
                                        error("arelle:loadFromSdmxMissingDSDForData", dsd_lookup_status_message)

                                # Update placeholder message based on DSD retrieval
                                payload_processed_at_least_partially = False
                                if retrieved_dsd:
                                    created_contexts = {}
                                    created_units = {}
                                    # Ensure factsInInstance and facts are initialized if this is the first data load
                                    if not hasattr(modelXbrl, "factsInInstance"): modelXbrl.factsInInstance = set()
                                    if not hasattr(modelXbrl, "facts"): modelXbrl.facts = []

                                    # Iterate through DataSet elements
                                    dataset_elements = xml_root.findall('m:DataSet', namespaces=ns)
                                    
                                    for dataset_el in dataset_elements:
                                        payload_processed_at_least_partially = True
                                        cntlr.addToLog(f"Processing DataSet. Attributes: {dict(dataset_el.attrib)}", messageCode="loadFromSdmx:info")
                                        
                                        # Determine the elements to iterate for observations (Series/Obs or direct Obs)
                                        # For StructureSpecificData, Obs are typically nested in Series.
                                        # For GenericData, Series and Obs can be mixed.
                                        # This example simplifies by checking for Series first.
                                        
                                        obs_container_elements = dataset_el.findall('Series') # Unqualified
                                        if not obs_container_elements: # If no Series, look for direct Obs
                                            obs_container_elements = dataset_el.findall('Obs')

                                        for item_el in obs_container_elements: # item_el is either a Series or a direct Obs
                                            is_series = item_el.tag == 'Series'
                                            
                                            dim_values_for_context = dict(item_el.attrib)
                                            
                                            # Entity Placeholder
                                            entity_scheme = "http://www.example.com/sdmx"
                                            entity_identifier = "DEFAULT_ENTITY"

                                            # Period Placeholder
                                            # In a real scenario, this would involve parsing the TIME_PERIOD value
                                            # and potentially other time-related attributes based on the DSD.
                                            sdmx_time_period_value = dim_values_for_context.get(retrieved_dsd.get('time_dimension', {}).get('id', 'TIME_PERIOD'))
                                            if sdmx_time_period_value:
                                                cntlr.addToLog(f"  SDMX TIME_PERIOD value: {sdmx_time_period_value}", messageCode="loadFromSdmx:info")
                                            # Placeholder Arelle period (instant)
                                            period_instant = dateTime("2023-01-01T00:00:00", type=DATETIME) # Using DATETIME for instant

                                            # Create Context Key
                                            # This needs to be refined based on actual dimension QNames and period parsing
                                            explicit_dim_qname_value_pairs = []
                                            for dim_id, dim_info in retrieved_dsd['dimensions'].items():
                                                sdmx_dim_value = dim_values_for_context.get(dim_id)
                                                if sdmx_dim_value:
                                                    # Placeholder for QName resolution
                                                    dim_qname_placeholder = qname(dim_info.get('concept_ref',{}).get('agencyID','SDMX'), dim_info.get('concept_ref',{}).get('id',dim_id))
                                                    
                                                    if dim_info.get('representation',{}).get('type') == 'codelist':
                                                        member_qname_placeholder = qname(dim_qname_placeholder.namespaceURI, f"{dim_qname_placeholder.localName}_Member_{sdmx_dim_value}")
                                                        explicit_dim_qname_value_pairs.append((dim_qname_placeholder, member_qname_placeholder))
                                                    else: # Typed dimension
                                                         explicit_dim_qname_value_pairs.append((dim_qname_placeholder, sdmx_dim_value))
                                            
                                            context_key_dims_tuple = tuple(sorted(explicit_dim_qname_value_pairs, key=lambda x: str(x[0])))
                                            context_key = (entity_identifier, entity_scheme, period_instant, frozenset(context_key_dims_tuple))

                                            current_context = None
                                            if context_key in created_contexts:
                                                current_context = created_contexts[context_key]
                                                cntlr.addToLog(f"    Reusing Context ID: {current_context.id}", messageCode="loadFromSdmx:info")
                                            else:
                                                context_id = f"c-{len(created_contexts) + 1}"
                                                qname_dims_for_arelle = {}
                                                for dim_qname_placeholder, member_value in explicit_dim_qname_value_pairs:
                                                    qname_dims_for_arelle[dim_qname_placeholder] = member_value
                                                
                                                current_context = modelXbrl.createContext(
                                                    entity_scheme,
                                                    entity_identifier,
                                                    'instant', # periodType, assuming instant for now
                                                    None, # periodStart, None for instant
                                                    period_instant, # periodEnd, used as the instant date
                                                    qname_dims_for_arelle, # dimensional aspects
                                                    id=context_id
                                                )
                                                created_contexts[context_key] = current_context
                                                cntlr.addToLog(f"    Created Context ID: {context_id} with dims: {qname_dims_for_arelle}", messageCode="loadFromSdmx:info")

                                            if is_series: # If item_el was a Series, now process its Obs
                                                for obs_el in item_el.findall('Obs'): # Unqualified
                                                    cntlr.addToLog(f"    Obs for Series: {dict(obs_el.attrib)} (Context: {current_context.id})", messageCode="loadFromSdmx:info")
                                                    # Fact creation logic for this obs_el would go here, using current_context
                                            else: # If item_el was a direct Obs
                                                cntlr.addToLog(f"  Direct Obs: {dict(item_el.attrib)} (Context: {current_context.id})", messageCode="loadFromSdmx:info")
                                                # Fact creation logic for this item_el (as obs_el) would go here

                                    if payload_processed_at_least_partially:
                                        missing.append(f"SDMX-ML data message ({msg_localname}): Context creation attempted. Unit/Fact creation and full DSD component mapping not yet implemented.")
                                    else: # DSD retrieved, but no DataSet elements found
                                        missing.append(f"SDMX-ML data message ({msg_localname}): DSD {active_dsd_key} retrieved, but no DataSet elements found or processed. Arelle fact creation not yet implemented.")
                                
                                else: # retrieved_dsd is None
                                    missing.append(f"SDMX-ML data message ({msg_localname}): DSD lookup failed ({dsd_lookup_status_message}). Payload parsing cannot proceed.")
                            
                            else: # Other message types like RegistryInterface, Error, Metadata messages
                                 missing.append(f"SDMX-ML message type {msg_localname} payload processing not yet defined.")

        except etree.LxmlError as e:
            missing.append(f"XML parsing error: {e}")
            error("arelle:loadFromSdmxXmlError", "XML parsing error in %(sdmxFile)s: %(error)s", sdmxFile=sdmxFile, error=e)
        except Exception as e:
            missing.append(f"Unexpected error during SDMX-ML processing: {e}")
            error("arelle:loadFromSdmxXmlError", "Unexpected error during SDMX-ML processing of %(sdmxFile)s: %(error)s - %(trace)s", 
                  sdmxFile=sdmxFile, error=e, trace=traceback.format_exc())

    else: # Not XML and not CSV starting with DSF pattern
        missing.append("Unable to determine SDMX file type (CSV or XML).")

    if missing:
        error("arelle:loadFromSdmxUnsupportedSdmxType",
              "; ".join(missing))
        return None

    # find map file
    # default is sdmx-xbrl-map.json in same directory as SDMX file or DTS
    mapFile = os.path.join(os.path.dirname(sdmxFile or modelXbrl.modelDocument.filepath), "sdmx-xbrl-map.json")
    if not os.path.exists(mapFile):
        error("arelle:loadFromSdmxMapFileNotFound",
              _("Map file not found: %(mapFile)s, for SDMX file: %(sdmxFile)s"),
              mapFile=mapFile, sdmxFile=sdmxFile)
        return None
    try:
        with io.open(mapFile, 'rt', encoding='utf-8') as fh:
            mapDoc = json.load(fh, object_pairs_hook=OrderedDict) # preserve order for determination of series keys
    except Exception as ex:
        error("arelle:loadFromSdmxMapFileNotReadable",
              _("Error reading map file: %(mapFile)s, error: %(error)s"),
              mapFile=mapFile, error=ex)
        return None

    # process map file
    # "dsd": "dsd file name or url"
    # "namespace": "target namespace for concepts"
    # "concepts": { sdmxName: conceptName ... }
    # "dimensions": [ (dimension concept, domain concept, member concept, isTyped, sdmxName) ... ]
    # "members": [ (dimension concept, domain concept, member concept, sdmxValue) ... ]
    # "measures": [ (measure concept, sdmxName) ... ]
    # "attributes": [ (attribute concept, sdmxName) ... ]
    # "units": { sdmxName: unitId ... }
    # "languages": { sdmxName: lang ... }

    dsdUrl = mapDoc.get("dsd")
    if dsdUrl and not isAbsolute(dsdUrl):
        dsdUrl = os.path.join(os.path.dirname(mapFile), dsdUrl)
    # for now, assume DSD is defined by mapDoc
    # TBD: load DSD if specified and use it to determine dimension names and order
    # for now, assume dimension names and order are from mapDoc

    namespace = mapDoc.get("namespace")
    if namespace is None:
        error("arelle:loadFromSdmxMapFileMissingNamespace",
              _("Map file missing namespace: %(mapFile)s"),
              mapFile=mapFile)
        return None

    # load concepts
    # sdmxName: conceptName
    conceptNames = mapDoc.get("concepts", {})

    # load dimensions
    # (dimension concept, domain concept, member concept, isTyped, sdmxName)
    dimMappings = OrderedDict() # sdmxName: (qnameDimConcept, qnameDomConcept, qnameMemConcept, isTyped)
    for dimItem in mapDoc.get("dimensions", []):
        if len(dimItem) == 5:
            dimConceptName, domConceptName, memConceptName, isTyped, sdmxDimName = dimItem
            dimMappings[sdmxDimName] = (qname(namespace, conceptNames.get(dimConceptName, dimConceptName)),
                                        qname(namespace, conceptNames.get(domConceptName, domConceptName)) if domConceptName else None,
                                        qname(namespace, conceptNames.get(memConceptName, memConceptName)) if memConceptName else None,
                                        isTyped)
        else:
            warning("arelle:loadFromSdmxMapFileDimensionSyntax",
                    _("Map file dimension item has %(count)s items, expected 5: %(item)s in %(mapFile)s"),
                    mapFile=mapFile, item=dimItem, count=len(dimItem))

    # load members
    # (dimension concept, domain concept, member concept, sdmxValue)
    memMappings = defaultdict(dict) # qnameDimConcept: {sdmxValue: qnameMemConcept}
    for memItem in mapDoc.get("members", []):
        if len(memItem) == 4:
            dimConceptName, domConceptName, memConceptName, sdmxValue = memItem
            dimConceptQn = qname(namespace, conceptNames.get(dimConceptName, dimConceptName))
            memConceptQn = qname(namespace, conceptNames.get(memConceptName, memConceptName))
            memMappings[dimConceptQn][sdmxValue] = memConceptQn
        else:
            warning("arelle:loadFromSdmxMapFileMemberSyntax",
                    _("Map file member item has %(count)s items, expected 4: %(item)s in %(mapFile)s"),
                    mapFile=mapFile, item=memItem, count=len(memItem))

    # load measures
    # (measure concept, sdmxName)
    measureMappings = {} # sdmxName: qnameMeasureConcept
    for measureItem in mapDoc.get("measures", []):
        if len(measureItem) == 2:
            measureConceptName, sdmxMeasureName = measureItem
            measureMappings[sdmxMeasureName] = qname(namespace, conceptNames.get(measureConceptName, measureConceptName))
        else:
            warning("arelle:loadFromSdmxMapFileMeasureSyntax",
                    _("Map file measure item has %(count)s items, expected 2: %(item)s in %(mapFile)s"),
                    mapFile=mapFile, item=measureItem, count=len(measureItem))

    # load attributes
    # (attribute concept, sdmxName)
    attributeMappings = {} # sdmxName: qnameAttrConcept
    for attrItem in mapDoc.get("attributes", []):
        if len(attrItem) == 2:
            attrConceptName, sdmxAttrName = attrItem
            attributeMappings[sdmxAttrName] = qname(namespace, conceptNames.get(attrConceptName, attrConceptName))
        else:
            warning("arelle:loadFromSdmxMapFileAttributeSyntax",
                    _("Map file attribute item has %(count)s items, expected 2: %(item)s in %(mapFile)s"),
                    mapFile=mapFile, item=attrItem, count=len(attrItem))

    # load units
    # sdmxName: unitId
    unitMappings = mapDoc.get("units", {})

    # load languages
    # sdmxName: lang
    languageMappings = mapDoc.get("languages", {})

    # process SDMX-CSV
    # header rows:
    #   dataflow,keyFamily,datastructureID (optional, for ECB's DSF)
    #   dimension names (except for last N columns which are OBS_VALUE and attributes)
    #   series attributes (blank above dimension names, values below series keys)
    # data rows:
    #   series keys (dimension values for series)
    #   observation value
    #   observation attributes

    # determine header rows and column definitions
    csvReader = csv.reader(io.StringIO(sdmxDoc))
    header = None # list of column header names
    seriesAttrs = None # list of series attribute names (same length as header)
    seriesAttrValues = None # list of series attribute values (same length as header)
    # find header row (dimension names)
    # this is the row before the one that starts with FREQ (ECB specific)
    # or the row that has OBS_VALUE in it
    # or the row where all cells are in dimMappings or measureMappings or attributeMappings
    headerRowFound = False
    headerLineNum = 0
    for i, row in enumerate(csvReader):
        headerLineNum = i
        if not headerRowFound:
            # check for OBS_VALUE (primary measure)
            if "OBS_VALUE" in row:
                header = row
                headerRowFound = True
            # check for all column names in mappings
            elif all(colName in dimMappings or colName in measureMappings or colName in attributeMappings
                     for colName in row if colName):
                header = row
                headerRowFound = True
            # check for FREQ in first column (ECB specific)
            # previous line must be header
            elif row and row[0] == CSV_seriesKeyFirstCol:
                # rewind to previous line to get header
                # (this requires re-opening the file or saving all lines read so far)
                # for now, assume header was found by OBS_VALUE check
                if header is None:
                    missing.append("Unable to determine header row for SDMX-CSV file.")
                break # data rows start here
        else: # header row found, now look for series attributes
            # series attributes are on a row after header, where cells are blank above dimension names
            # and have values below series attribute names
            isSeriesAttrRow = True
            hasSeriesAttrValues = False
            for j, colName in enumerate(row):
                if header[j] in dimMappings: # dimension column
                    if colName: # should be blank
                        isSeriesAttrRow = False
                        break
                elif colName: # series attribute value
                    hasSeriesAttrValues = True
            if isSeriesAttrRow and hasSeriesAttrValues:
                seriesAttrs = header # attribute names are in the header row
                seriesAttrValues = row # attribute values are in this row
                # TBD remove series attributes from header list?
            break # data rows start here (or after series attributes row)

    if missing:
        error("arelle:loadFromSdmxCsvError",
              "; ".join(missing) + " in file %(sdmxFile)s",
              sdmxFile=sdmxFile)
        return None

    if header is None:
        error("arelle:loadFromSdmxCsvNoHeader",
              _("Unable to determine header row for SDMX-CSV file: %(sdmxFile)s"),
              sdmxFile=sdmxFile)
        return None

    # determine dimension columns, measure columns, attribute columns
    dimCols = [] # list of (index, sdmxDimName, qnameDimConcept, qnameDomConcept, qnameMemConcept, isTyped)
    measureCols = [] # list of (index, sdmxMeasureName, qnameMeasureConcept)
    attrCols = [] # list of (index, sdmxAttrName, qnameAttrConcept)
    obsValueCol = -1
    timePeriodCol = -1
    obsAttributes = {} # colIndex: qnameAttrConcept for attributes attached to OBS_VALUE

    for i, colName in enumerate(header):
        if not colName: continue # skip empty column names
        if colName in dimMappings:
            qnameDimConcept, qnameDomConcept, qnameMemConcept, isTyped = dimMappings[colName]
            dimCols.append( (i, colName, qnameDimConcept, qnameDomConcept, qnameMemConcept, isTyped) )
            if colName == "TIME_PERIOD": # SDMX standard time dimension
                timePeriodCol = i
        elif colName in measureMappings:
            qnameMeasureConcept = measureMappings[colName]
            measureCols.append( (i, colName, qnameMeasureConcept) )
            if colName == "OBS_VALUE":
                obsValueCol = i
        elif colName in attributeMappings:
            qnameAttrConcept = attributeMappings[colName]
            attrCols.append( (i, colName, qnameAttrConcept) )
            # determine if attribute is attached to OBS_VALUE or series/group/dataset
            # for now, assume attached to OBS_VALUE if colName is after OBS_VALUE col
            # (this is not robust, need DSD to determine this)
            if obsValueCol != -1 and i > obsValueCol:
                obsAttributes[i] = qnameAttrConcept


    if obsValueCol == -1 and not measureCols: # if no OBS_VALUE, assume first measure is primary measure
        if measureCols:
            obsValueCol = measureCols[0][0]
        else: # if no measures defined, assume OBS_VALUE is primary measure (and was omitted from map)
            # try to find OBS_VALUE in header anyway
            try:
                obsValueCol = header.index("OBS_VALUE")
            except ValueError:
                pass # not found

    if obsValueCol == -1:
        error("arelle:loadFromSdmxCsvNoObsValue",
              _("Unable to determine OBS_VALUE (primary measure) column for SDMX-CSV file: %(sdmxFile)s"),
              sdmxFile=sdmxFile)
        return None

    # create context ID pattern based on dimension names (excluding TIME_PERIOD)
    # sort by dimension qname for consistency
    # include entity identifier and period
    # dimensions are added if not mapped to period start/end/instant
    # context ID pattern is _ αντί για : in qnames
    cntxIdPattern = "{entity}_{period}"
    sortedDimCols = sorted(dimCols, key=lambda item: item[2]) # sort by qnameDimConcept
    for i, colName, qnameDimConcept, qnameDomConcept, qnameMemConcept, isTyped in sortedDimCols:
        if colName != "TIME_PERIOD":
            cntxIdPattern += "_{" + colName.replace(":","_") + "}"


    # create unit ID pattern based on measure and unit names
    # unit ID pattern is measureName_unitName
    # TBD: how to determine unit from SDMX-CSV?
    # for now, assume all numeric facts have same unit, taken from first unit mapping if any
    # or if OBS_UNIT column exists, use that
    # or if unit is specified in map file for OBS_VALUE measure, use that
    unitId = "uPure" # default if no unit mapping
    if unitMappings:
        unitId = list(unitMappings.values())[0]
    if "OBS_UNIT" in header:
        obsUnitCol = header.index("OBS_UNIT")
    else:
        obsUnitCol = -1


    # find existing facts to avoid duplicates
    # key is (conceptQn, contextID, unitID, lang)
    # for numeric facts, value is fact value (for comparing if different)
    # for non-numeric facts, value is True
    existingFacts = {}
    for fact in modelXbrl.facts:
        if fact.isNumeric:
            existingFacts[(fact.qname, fact.contextID, fact.unitID, fact.xmlLang)] = fact.value
        else:
            existingFacts[(fact.qname, fact.contextID, fact.unitID, fact.xmlLang)] = True


    # process data rows
    # each row is a series of observations or a single observation
    # if series, first N cells are dimension values (series keys)
    # then OBS_VALUE and observation attributes
    # if single observation, all dimension values are present on the row

    # need to determine if file is series-oriented or observation-oriented
    # series-oriented if first data row has fewer values than header row
    # (series keys followed by first observation)
    # observation-oriented if first data row has same number of values as header row
    # (all dimensions present for each observation)

    # rewind csv reader to first data row
    # this requires re-opening file or saving all lines read so far
    # for now, re-open file and skip header rows
    try:
        csvReader = csv.reader(io.StringIO(sdmxDoc))
        for i in range(headerLineNum + 1): # skip header and pre-header rows
            next(csvReader)
        if seriesAttrValues: # skip series attribute values row
            next(csvReader)
    except StopIteration: # no data rows
        warning("arelle:loadFromSdmxCsvNoDataRows",
                _("No data rows found in SDMX-CSV file: %(sdmxFile)s"),
                sdmxFile=sdmxFile)
        return None


    # process data rows
    instance = modelXbrl.modelDocument
    defaultLang = modelXbrl.modelManager.defaultLang
    newFactIDs = set() # new fact IDs created in this load
    numFactsLoaded = 0
    numFactsSkipped = 0

    # entity identifier for all facts (usually from instance, or could be from SDMX attribute)
    # for now, use first entity identifier in instance
    entityIdentScheme = "http://www.xbrl.org/taxonomy/int/id" # default if not in instance
    entityIdentValue = "0" # default if not in instance
    if modelXbrl.contexts:
        context = modelXbrl.contexts[list(modelXbrl.contexts.keys())[0]] # take first context
        entityIdentScheme = context.entityIdentifier[0]
        entityIdentValue = context.entityIdentifier[1]


    seriesKeys = None # for series-oriented data
    for i, row in enumerate(csvReader):
        if not row or not any(row): continue # skip empty rows

        # determine if this row is series keys or observation data
        # if fewer cells than header, it's series keys (dimension values for the series)
        # otherwise it's observation data (all dimensions present)
        isSeriesKeysRow = (len(row) < len(header))

        if isSeriesKeysRow:
            seriesKeys = row
            continue # next row has first observation for this series
        else: # observation data row
            if seriesKeys: # combine with series keys to get full dimension set for this observation
                # series keys are first N cells, observation data is rest
                # TBD: need to know how many series keys there are
                # for now, assume series keys are all but last M cells (obs_value + obs_attributes)
                numObsCells = 1 + len(obsAttributes)
                numSeriesKeys = len(header) - numObsCells
                dimValues = list(seriesKeys[0:numSeriesKeys]) # copy series keys
                dimValues.extend( row[numSeriesKeys:] ) # add observation-specific dimensions (if any) and obs_value/attrs
                # above is probably wrong...
                # better: seriesKeys provides values for first N dimension columns
                # row provides values for remaining dimension columns (if any) and obs_value/attrs
                # for now, assume all dimensions are in series keys if seriesKeys is not None
                # and row only has obs_value and obs_attrs
                # so effectively, dimValues comes from seriesKeys, and obs_value/attrs from row
                # this means row should have only numObsCells values
                # this needs to be more robust based on DSD structure or CSV guidelines
                # for now, assume if seriesKeys is set, then row contains only obs_value and obs_attrs
                # and dim values are all from seriesKeys
                # this implies that seriesKeys should have values for ALL dimension columns
                # and row should start at obsValueCol index effectively
                # This is probably wrong for general SDMX-CSV.
                #
                # Alternative: SDMX-CSV Guidelines section 3.2.2 says:
                # "Data messages MAY optionally repeat the full series key on every row.
                #  Alternatively, the series key MAY be included only on the first row for that series."
                # This suggests if seriesKeys is set, then current row is just obs_value and obs_attrs
                # and dimensions are from seriesKeys.
                # If seriesKeys is NOT set, then current row has all dimensions AND obs_value/attrs.
                # Let's try that logic.

                # If seriesKeys is active, then this row provides obs_value and obs_attrs
                # The dimension values are taken from seriesKeys
                # We need to map seriesKeys (list of values) to the dimension columns
                # seriesKeys should have one value for each dimension column
                obsRow = row # save original row for obs_value and obs_attrs
                row = list(seriesKeys) # now use seriesKeys as the source for dimension values
                                       # and extend it with dummy values for measure/attr columns
                                       # so it has same length as header for zipping
                row.extend( [None] * (len(header) - len(row)) )


            # build fact context and unit
            cntxDimValues = {} # sdmxDimName: value
            periodStart = periodEnd = periodInstant = None
            factAttrs = {} # qnameAttr: value

            # process dimension values from current row
            for colIndex, sdmxDimName, qnameDimConcept, qnameDomConcept, qnameMemConcept, isTyped in dimCols:
                if colIndex >= len(row) or not row[colIndex]: # no value for this dimension
                    # TBD: should this be an error or warning? or handled by validation?
                    # for now, skip this fact if a required dimension is missing
                    # how to know if required? for now, assume all dimensions are required
                    # unless it's TIME_PERIOD which is handled separately
                    if sdmxDimName != "TIME_PERIOD":
                        warning("arelle:loadFromSdmxCsvMissingDimValue",
                                _("Missing value for dimension %(sdmxDimName)s in row %(rowNum)s, skipping fact."),
                                sdmxDimName=sdmxDimName, rowNum=i+headerLineNum+1)
                        cntxDimValues = None # flag to skip fact
                        break
                    else: # time period is special, can be derived from start/end/instant
                        continue # process other dimensions

                dimValue = row[colIndex].strip()

                if sdmxDimName == "TIME_PERIOD":
                    # parse time period (ISO 8601 duration PnYnMnD, or date/dateTime)
                    # TBD: support other SDMX time formats (e.g. YYYY-S1, YYYY-Q1, YYYY-MM, YYYY)
                    # these need to be converted to XBRL periods (duration or instant)
                    # for now, assume ISO 8601 date or dateTime
                    try:
                        dt = dateTime(dimValue, type=DATEUNION, castException=ValueError)
                        if dt.dateOnly: # date
                            periodInstant = dateunionDate(dt)
                        else: # dateTime
                            periodInstant = dt
                    except ValueError:
                        warning("arelle:loadFromSdmxCsvInvalidTimePeriod",
                                _("Invalid TIME_PERIOD value %(value)s in row %(rowNum)s, attempting to parse as duration."),
                                value=dimValue, rowNum=i+headerLineNum+1)
                        # try parsing as duration PnYnMnD or PnW
                        # TBD: this is complex, for now just support YYYY-MM as start/end of month
                        if len(dimValue) == 7 and dimValue[4] == '-': # YYYY-MM
                            try:
                                year = int(dimValue[0:4])
                                month = int(dimValue[5:7])
                                periodStart = datetime.date(year, month, 1)
                                periodEnd = datetime.date(year, month, monthrange(year,month)[1])
                            except ValueError:
                                warning("arelle:loadFromSdmxCsvInvalidTimePeriod",
                                        _("Invalid TIME_PERIOD value %(value)s in row %(rowNum)s, skipping fact."),
                                        value=dimValue, rowNum=i+headerLineNum+1)
                                cntxDimValues = None # flag to skip fact
                                break
                        else: # unknown time period format
                             warning("arelle:loadFromSdmxCsvInvalidTimePeriod",
                                    _("Unsupported TIME_PERIOD value %(value)s in row %(rowNum)s, skipping fact."),
                                    value=dimValue, rowNum=i+headerLineNum+1)
                             cntxDimValues = None # flag to skip fact
                             break
                    continue # done with TIME_PERIOD

                # non-time dimension
                if isTyped:
                    cntxDimValues[sdmxDimName] = dimValue # store original sdmx value for context ID
                    # create typed dimension element in instance
                    # TBD: need to add this to a segment or scenario in context
                    # for now, just store value, will be added when context is created
                else: # explicit dimension
                    # map sdmxValue to member concept qname
                    qnameMem = memMappings.get(qnameDimConcept, {}).get(dimValue)
                    if qnameMem is None:
                        warning("arelle:loadFromSdmxCsvMissingMemberMapping",
                                _("Missing mapping for dimension %(sdmxDimName)s value %(value)s in row %(rowNum)s, skipping fact."),
                                sdmxDimName=sdmxDimName, value=dimValue, rowNum=i+headerLineNum+1)
                        cntxDimValues = None # flag to skip fact
                        break
                    cntxDimValues[sdmxDimName] = qnameMem # store member qname for context ID

            if cntxDimValues is None: # problem with dimensions, skip fact
                numFactsSkipped += 1
                continue


            # create context
            # use periodInstant or periodStart/End
            if periodInstant:
                period = ModelInstanceObject.createContextPeriod(modelXbrl, periodInstant)
            elif periodStart and periodEnd:
                period = ModelInstanceObject.createContextPeriod(modelXbrl, periodStart, periodEnd)
            else: # no period defined for fact (e.g. if TIME_PERIOD was missing or invalid)
                warning("arelle:loadFromSdmxCsvMissingPeriod",
                        _("Missing or invalid period for fact in row %(rowNum)s, skipping fact."),
                        rowNum=i+headerLineNum+1)
                numFactsSkipped += 1
                continue

            # build context ID from pattern
            # need to replace {dimName} with actual value or qname string for explicit dims
            # qnames in context ID use _ instead of :
            cntxIdFormatValues = {"entity": entityIdentValue.replace(":","_"),
                                  "period": period.periodId} # TBD: periodId might not be unique enough
            for sdmxDimName, qnameDimConcept, qnameDomConcept, qnameMemConcept, isTyped in dimCols:
                if sdmxDimName != "TIME_PERIOD":
                    if isTyped:
                        cntxIdFormatValues[sdmxDimName.replace(":","_")] = cntxDimValues[sdmxDimName]
                    else: # explicit, value is qnameMem
                        cntxIdFormatValues[sdmxDimName.replace(":","_")] = cntxDimValues[sdmxDimName].localName # TBD: use clark notation string?

            contextID = cntxIdPattern.format(**cntxIdFormatValues)

            # get or create context
            context = modelXbrl.contexts.get(contextID)
            if context is None:
                context = ModelInstanceObject.createContext(modelXbrl,
                                                            entityIdentScheme, entityIdentValue,
                                                            period,
                                                            contextID)
                # add dimensions to context
                for sdmxDimName, qnameDimConcept, qnameDomConcept, qnameMemConcept, isTyped in dimCols:
                    if sdmxDimName != "TIME_PERIOD":
                        dimVal = cntxDimValues[sdmxDimName]
                        if isTyped:
                            # create typed dimension element
                            # TBD: need to get schema type for typed dimension from DSD or map
                            # for now, assume string
                            typedMember = XmlUtil.addChild(context.segmentOrScenario, qnameDimConcept, text=dimVal)
                            # TBD: do we need domain for typed dimension?
                        else: # explicit dimension
                            explMember = XmlUtil.addChild(context.segmentOrScenario, qnameDimConcept, text=dimVal.clarkNotation) # use qnameMem
                            XmlUtil.setattr(explMember, XbrlConst.qnXbrliDimensionDomain, qnameDomConcept.clarkNotation) # use qnameDom

            # process measure value (OBS_VALUE)
            if obsValueCol >= len(row) or not row[obsValueCol]:
                # no primary measure value, treat as nil fact if allowed, else skip
                # TBD: how to know if nil is allowed? for now, skip
                warning("arelle:loadFromSdmxCsvMissingObsValue",
                        _("Missing OBS_VALUE in row %(rowNum)s, skipping fact."),
                        rowNum=i+headerLineNum+1)
                numFactsSkipped += 1
                continue

            obsValue = row[obsValueCol].strip()
            qnameMeasure = measureMappings.get("OBS_VALUE") or measureCols[0][2] # from mapping or first measure col

            # determine unit
            # if OBS_UNIT column exists, use its value to lookup unitId in unitMappings
            # else use default unitId
            currentUnitId = unitId # default
            if obsUnitCol != -1 and obsUnitCol < len(row) and row[obsUnitCol]:
                sdmxUnit = row[obsUnitCol].strip()
                if sdmxUnit in unitMappings:
                    currentUnitId = unitMappings[sdmxUnit]
                else:
                    warning("arelle:loadFromSdmxCsvUnknownUnit",
                            _("Unknown unit %(sdmxUnit)s in row %(rowNum)s, using default unit %(unitId)s."),
                            sdmxUnit=sdmxUnit, rowNum=i+headerLineNum+1, unitId=currentUnitId)

            unit = modelXbrl.units.get(currentUnitId)
            if unit is None:
                # create unit (assume simple measure, no numerator/denominator)
                # TBD: support complex units from DSD or map
                unit = ModelInstanceObject.createUnit(modelXbrl, [currentUnitId], [], currentUnitId)


            # process observation attributes (attached to OBS_VALUE fact)
            # these are in obsAttributes dict (colIndex: qnameAttrConcept)
            # values are from current row (if seriesKeys active, use obsRow for these)
            sourceRowForAttrs = obsRow if seriesKeys else row
            for colIndex, qnameAttrConcept in obsAttributes.items():
                if colIndex < len(sourceRowForAttrs) and sourceRowForAttrs[colIndex]:
                    attrValue = sourceRowForAttrs[colIndex].strip()
                    # TBD: handle data types of attributes (e.g. date, boolean)
                    # for now, assume string
                    factAttrs[qnameAttrConcept] = attrValue


            # process series attributes (attached to all facts in series)
            if seriesAttrs and seriesAttrValues:
                for j, attrName in enumerate(seriesAttrs):
                    if attrName in attributeMappings and seriesAttrValues[j]:
                        qnameAttrConcept = attributeMappings[attrName]
                        attrValue = seriesAttrValues[j].strip()
                        factAttrs[qnameAttrConcept] = attrValue
                        # TBD: check for conflict with obsAttributes (which should win?)


            # TBD: process group attributes (attach to facts in group)
            # TBD: process dataset attributes (attach to all facts in dataset)


            # create fact
            # check for duplicates first
            # key is (conceptQn, contextID, unitID, lang)
            # for numeric facts, value is fact value (for comparing if different)
            # for non-numeric facts, value is True
            factLang = defaultLang # TBD: get lang from OBS_LANG column if present
            if "OBS_LANG" in header:
                obsLangCol = header.index("OBS_LANG")
                if obsLangCol < len(sourceRowForAttrs) and sourceRowForAttrs[obsLangCol]:
                    sdmxLang = sourceRowForAttrs[obsLangCol].strip()
                    if sdmxLang in languageMappings:
                        factLang = languageMappings[sdmxLang]
                    else:
                        warning("arelle:loadFromSdmxCsvUnknownLang",
                                _("Unknown language %(sdmxLang)s in row %(rowNum)s, using default language %(lang)s."),
                                sdmxLang=sdmxLang, rowNum=i+headerLineNum+1, lang=factLang)


            # determine decimals and precision based on value
            # TBD: get from DSD if available (e.g. NUM_DECIMALS attribute)
            decimals = "INF" # default for non-numeric or if cannot determine
            precision = "INF"
            if obsValue.replace('.','',1).isdigit(): # check if numeric (handles positive/negative integers/floats)
                if '.' in obsValue:
                    decimals = len(obsValue.split('.',1)[1])
                else:
                    decimals = 0
                precision = len(obsValue.replace('.',''))


            factKey = (qnameMeasure, contextID, currentUnitId if unit else None, factLang if qnameMeasure.modelObject.isXbrlText else None)
            if factKey in existingFacts:
                # if numeric, check if value is different (within tolerance?)
                # if non-numeric, assume duplicate if key matches
                # TBD: tolerance for numeric comparison
                if qnameMeasure.modelObject.isNumeric:
                    if existingFacts[factKey] == obsValue: # TBD: type conversion needed?
                        numFactsSkipped += 1
                        continue # skip duplicate fact
                    else: # different value for same fact, treat as error or overwrite?
                        # for now, skip and warn
                        warning("arelle:loadFromSdmxCsvDuplicateFactDifferentValue",
                                _("Fact for %(concept)s context %(contextID)s unit %(unitID)s lang %(lang)s already exists with different value %(oldValue)s, new value %(newValue)s, skipping."),
                                concept=qnameMeasure, contextID=contextID, unitID=currentUnitId, lang=factLang,
                                oldValue=existingFacts[factKey], newValue=obsValue)
                        numFactsSkipped += 1
                        continue
                else: # non-numeric, already exists
                    numFactsSkipped += 1
                    continue # skip duplicate fact


            # create fact attributes dictionary for createFact
            attrs = list(factAttrs.items()) # list of (qname, value) tuples
            if qnameMeasure.modelObject.isNumeric: # add decimals/precision if numeric
                attrs.append( ("decimals", decimals) )
                attrs.append( ("precision", precision) )
            elif qnameMeasure.modelObject.isXbrlText and factLang: # add xml:lang if text and lang specified
                attrs.append( (XbrlConst.qnXmlLang, factLang) )


            f = modelXbrl.createFact(qnameMeasure, attributes=attrs, parent=instance.xmlRootElement,
                                     unit=unit, context=context, value=obsValue)
            if f is not None:
                newFactIDs.add(f.id)
                numFactsLoaded += 1
                existingFacts[factKey] = obsValue # add to existing facts to prevent further duplicates from this load

                # validate fact dimensionally (if DTR is loaded)
                # TBD: this might be slow if many facts, maybe do once at end?
                # for now, validate each fact as it's created
                if modelXbrl.hasXDT:
                    if not isFactDimensionallyValid(modelXbrl, f):
                        error("arelle:loadFromSdmxXdtError",
                              _("Fact does not conform to dimensional assertions: %(fact)s"),
                              fact=f.href(viewable=True) or f.id, modelObject=f)


    if numFactsLoaded > 0:
        info("arelle:loadFromSdmxComplete",
             _("Loaded %(numFactsLoaded)s facts, skipped %(numFactsSkipped)s duplicate or invalid facts, from SDMX file: %(sdmxFile)s"),
             numFactsLoaded=numFactsLoaded, numFactsSkipped=numFactsSkipped, sdmxFile=sdmxFile)
    else:
        warning("arelle:loadFromSdmxNoFactsLoaded",
                _("No facts loaded from SDMX file: %(sdmxFile)s (skipped %(numFactsSkipped)s facts)"),
                sdmxFile=sdmxFile, numFactsSkipped=numFactsSkipped)

    # revalidate instance if new facts were added
    if newFactIDs:
        # TBD: need to re-run full validation, or just specific checks?
        # for now, assume caller will handle revalidation if needed
        # modelXbrl.modelManager.validator.validate(modelXbrl, newFactIDs)
        pass

    return modelXbrl


def loadFromSdmxMenuEntender(cntlr, menu, *args, **kwargs):
    # Extend menu with an item for the save infoset plugin
    menu.add_command(label="Load from SDMX",
                     underline=0,
                     command=lambda: loadFromSdmxMenuCommand(cntlr, **kwargs) )

def loadFromSdmxMenuCommand(cntlr, **kwargs):
    # get instances menu
    # if no instance loaded, disable
    if cntlr.modelManager is None or cntlr.modelManager.modelXbrl is None:
        cntlr.addToLog("No instance selected.")
        return

    modelXbrl = cntlr.modelManager.modelXbrl
    if modelXbrl.modelDocument is None or modelXbrl.modelDocument.type not in (ModelDocument.Type.INSTANCE, ModelDocument.Type.INLINEXBRL):
        cntlr.addToLog("No instance document is loaded.")
        return

    # ask for SDMX file
    sdmxFile = cntlr.uiFileDialog("open",
                                 title=_("Open SDMX file for loading into instance"),
                                 initialdir=os.path.dirname(modelXbrl.modelDocument.filepath),
                                 filetypes=[(_("SDMX files"), "*.*")], # TBD: specific extensions? .xml, .csv, .dsf
                                 defaultextension=".xml") # TBD
    if not sdmxFile:
        return

    try:
        loadFromSdmx(cntlr, cntlr.addToLog, cntlr.addToLog, modelXbrl, sdmxFile, sdmxFile) # sdmxUrl = sdmxFile for now
    except Exception as ex:
        import traceback
        cntlr.addToLog(_("[Exception] Load from SDMX exception: %(error)s at %(trace)s"),
                       error=ex, trace=traceback.format_exc(), exc_info=True)


def loadFromSdmxCommandLineOptionExtender(parser, *args, **kwargs):
    # extend command line options with a save DTS option
    parser.add_option("--load-from-sdmx",
                      action="store",
                      dest="loadFromSdmxFile",
                      help=_("Load facts from an SDMX file into the current instance. "
                             "Requires an instance to be loaded first. "
                             "A map file (sdmx-xbrl-map.json) must be in the same directory as the SDMX file or DTS. "
                             "Value is the SDMX file path."))

def loadFromSdmxCommandLineXbrlLoaded(cntlr, options, modelXbrl, *args, **kwargs):
    # if loading from SDMX is requested, do it now
    if getattr(options, "loadFromSdmxFile", None):
        if modelXbrl is None or modelXbrl.modelDocument is None or \
           modelXbrl.modelDocument.type not in (ModelDocument.Type.INSTANCE, ModelDocument.Type.INLINEXBRL):
            cntlr.addToLog("No instance document is loaded for loading from SDMX.", messageCode="arelle:loadFromSdmxNoInstance")
            return # ignore if no instance is loaded (e.g. if just validating a taxonomy)

        sdmxFile = options.loadFromSdmxFile
        # TBD: need sdmxUrl if different from sdmxFile (e.g. web service)
        try:
            loadFromSdmx(cntlr, cntlr.addToLog, cntlr.addToLog, modelXbrl, sdmxFile, sdmxFile)
        except Exception as ex:
            import traceback
            cntlr.addToLog(_("[Exception] Load from SDMX exception: %(error)s at %(trace)s"),
                           error=ex, trace=traceback.format_exc(), exc_info=True)


__pluginInfo__ = {
    'name': 'Load From SDMX',
    'version': '0.9',
    'description': "This plugin loads facts from an SDMX-CSV file into an XBRL instance, "
                   "mapping SDMX dimensions and measures to XBRL concepts using a JSON map file.",
    'license': 'Apache-2',
    'author': 'Mark V Systems Limited',
    'copyright': '(c) Copyright 2016-2022 Mark V Systems Limited, All rights reserved.',
    # classes of mount points (plugins)
    'ModelDocument.FiletypeRecognized': isSdmxLoadable,
    'ModelDocument.Load': sdmxLoader,
    'CntlrWinMain.Menu.Tools': loadFromSdmxMenuEntender, # Optional: Keep GUI menu
    'CntlrCmdLine.Options': loadFromSdmxCommandLineOptionExtender, # Optional: Keep command line option
    'CntlrCmdLine.Xbrl.Loaded': loadFromSdmxCommandLineXbrlLoaded, # Optional: Keep command line loader
}
