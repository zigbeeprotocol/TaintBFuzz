#define ZCLTestID 		6
#define ZCL_TEST_ENDPOINT  	8

const uint16 zclTest_clusterRevision_all = 0x0001; 

const uint8 zclTest_HWRevision = 1;
const uint8 zclTest_ZCLVersion = 1;
const uint8 zclTest_ManufacturerName[] = { 16, 'Z','F','u','z','z','e','r',' ',' ',' ',' ',' ',' ',' ',' ',' ' };
const uint8 zclTest_ModelId[] = { 16, 'U','T','A','C','S','E',' ',' ',' ',' ',' ',' ',' ',' ',' ',' ' };
const uint8 zclTest_DateCode[] = { 16, '2','0','1','9','1','0','3','1',' ',' ',' ',' ',' ',' ',' ',' ' };
const uint8 zclTest_PowerSource = 0x01;

uint8 zclTest_LocationDescription[] = { 16, ' ',' ',' ',' ',' ',' ',' ',' ',' ',' ',' ',' ',' ',' ',' ',' ' };
uint8 zclTest_PhysicalEnvironment = 0;
uint8 zclTest_DeviceEnable = 0x01;

uint16 zclTest_IdentifyTime;

uint8 zclTestSeq = 1;

const cId_t zclTest_InClusterList[] =
{
  0x0000,
  0x0003,
  0x0007,
};
#define ZCLTEST_MAX_INCLUSTERS   (sizeof(zclTest_InClusterList) / sizeof(zclTest_InClusterList[0]))


const cId_t zclTest_OutClusterList[] =
{
  0x0000,
  0x0007,
};
#define ZCLTEST_MAX_OUTCLUSTERS  (sizeof(zclTest_OutClusterList) / sizeof(zclTest_OutClusterList[0]))


#define TEST_MAX_OPTIONS	1

zclOptionRec_t zclBasic_Test_Options[TEST_MAX_OPTIONS] =
{
  {
    0x0000,
    (0x40 | 0x10),
  },
};

SimpleDescriptionFormat_t zclTest_SimpleDesc =
{
  8,                  	//  int Endpoint;
  0x0104,                    //  uint16 AppProfId;
  0x0000,        //  uint16 AppDeviceId;
  0,            		//  int   AppDevVer:4;
  0,                     		//  int   AppFlags:4;
  ZCLTEST_MAX_INCLUSTERS,         		//  byte  AppNumInClusters;
  (cId_t *)zclTest_InClusterList, 		//  byte *pAppInClusterList;
  ZCLTEST_MAX_OUTCLUSTERS,        		//  byte  AppNumInClusters;
  (cId_t *)zclTest_OutClusterList 		//  byte *pAppInClusterList;
};

endPointDesc_t zclTest_epDesc = {
    .endPoint = ZCL_TEST_ENDPOINT,
    .task_id = (uint8 *)ZCLTestID,
    .simpleDesc = &zclTest_SimpleDesc
};

// Used to assign to global variable attrList for zclFindAttrRecsList
CONST zclAttrRec_t zclTest_Attrs_All[] =
{
  #ifdef ZCL_IDENTIFY
  // *** Identify Cluster Attribute ***
  {
    ZCL_CLUSTER_ID_GEN_IDENTIFY,
    { // Attribute record
      ATTRID_IDENTIFY_TIME,
      ZCL_DATATYPE_UINT16,
      (ACCESS_CONTROL_READ | ACCESS_CONTROL_WRITE),
      (void *)&zclTest_IdentifyTime
    }
  },
  #endif
  // *** General Basic Cluster Attributes ***
  {
    ZCL_CLUSTER_ID_GEN_BASIC,             
    {  // Attribute record
      ATTRID_BASIC_HW_VERSION,            
      ZCL_DATATYPE_UINT8,                 
      ACCESS_CONTROL_READ,                
      (void *)&zclTest_HWRevision 
    }
  },
  {
    ZCL_CLUSTER_ID_GEN_BASIC,
    { // Attribute record
      ATTRID_BASIC_ZCL_VERSION,
      ZCL_DATATYPE_UINT8,
      ACCESS_CONTROL_READ,
      (void *)&zclTest_ZCLVersion
    }
  },
  {
    ZCL_CLUSTER_ID_GEN_BASIC,
    { // Attribute record
      ATTRID_BASIC_MANUFACTURER_NAME,
      ZCL_DATATYPE_CHAR_STR,
      ACCESS_CONTROL_READ,
      (void *)zclTest_ManufacturerName
    }
  },
  {
    ZCL_CLUSTER_ID_GEN_BASIC,
    { // Attribute record
      ATTRID_BASIC_MODEL_ID,
      ZCL_DATATYPE_CHAR_STR,
      ACCESS_CONTROL_READ,
      (void *)zclTest_ModelId
    }
  },
  {
    ZCL_CLUSTER_ID_GEN_BASIC,
    { // Attribute record
      ATTRID_BASIC_DATE_CODE,
      ZCL_DATATYPE_CHAR_STR,
      ACCESS_CONTROL_AUTH_READ,
      (void *)zclTest_DateCode
    }
  },
  {
    ZCL_CLUSTER_ID_GEN_BASIC,
    { // Attribute record
      ATTRID_BASIC_POWER_SOURCE,
      ZCL_DATATYPE_ENUM8,
      ACCESS_CONTROL_READ,
      (void *)&zclTest_PowerSource
    }
  },
  {
    ZCL_CLUSTER_ID_GEN_BASIC,
    { // Attribute record
      ATTRID_BASIC_LOCATION_DESC,
      ZCL_DATATYPE_CHAR_STR,
      (ACCESS_CONTROL_READ | ACCESS_CONTROL_WRITE),
      NULL
    }
  },
  {
    ZCL_CLUSTER_ID_GEN_BASIC,
    { // Attribute record
      ATTRID_BASIC_PHYSICAL_ENV,
      ZCL_DATATYPE_ENUM8,
      (ACCESS_CONTROL_READ | ACCESS_CONTROL_WRITE),
      (void *)&zclTest_PhysicalEnvironment
    }
  },
  {
    ZCL_CLUSTER_ID_GEN_BASIC,
    { // Attribute record
      ATTRID_BASIC_DEVICE_ENABLED,
      ZCL_DATATYPE_BOOLEAN,
      (ACCESS_CONTROL_READ | ACCESS_CONTROL_WRITE),
      (void *)&zclTest_DeviceEnable
    }
  },
  {
    ZCL_CLUSTER_ID_GEN_BASIC,
    {  // Attribute record
      ATTRID_CLUSTER_REVISION,
      ZCL_DATATYPE_UINT16,
      ACCESS_CONTROL_READ,
      (void *)&zclTest_clusterRevision_all
    }
  },
  {
    ZCL_CLUSTER_ID_GEN_IDENTIFY,
    {  // Attribute record
      ATTRID_CLUSTER_REVISION,
      ZCL_DATATYPE_UINT16,
      ACCESS_CONTROL_READ,
      (void *)&zclTest_clusterRevision_all
    }
  },
};
CONST zclAttrRecsList zclTest_AttrList = {
	.endpoint = ZCL_TEST_ENDPOINT,
	.attrs = zclTest_Attrs_All,
	.numAttributes = sizeof(zclTest_Attrs_All) / sizeof(zclTest_Attrs_All[0]),
	.next = (zclAttrRecsList *)NULL,
};

// Used to assign to global variable gpCmdList for zclFindCmdRecsList
CONST zclCommandRec_t zclTest_Cmds_Basic[] =
{
  {
    ZCL_CLUSTER_ID_GEN_BASIC,
    COMMAND_BASIC_RESET_FACT_DEFAULT,
    CMD_DIR_SERVER_RECEIVED
  },
  
};

CONST zclCmdRecsList_t zclTest_CmdList = {
	.endpoint = ZCL_TEST_ENDPOINT,
	.pCmdRecs = zclTest_Cmds_Basic,
	.numCommands = sizeof(zclTest_Cmds_Basic) / sizeof(zclTest_Cmds_Basic[0]),
	.pNext = (zclCommandRec_t *)NULL,
};
