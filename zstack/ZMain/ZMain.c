#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <ctype.h>

#ifndef NONWK
  #include "AF.h"
#endif

#include "OSAL.h"
#include "OSAL_Memory.h"
#include "zcl.h"
#include "zcl_ha.h"
#include "zcl_genericapp.h"
#include "zcl_diagnostic.h"
#include "hal_drivers.h"
#include "APS.h"
#include "ZDApp.h"
#include "bdb_interface.h"
#include "ZConfig.h"

/********************************
 * Local Functions Declaration
 ********************************/
static void initialization();
static void initSourceEP(void);
static void initDestAddr(void);
static void process_no_caller_funcs(afIncomingMSGPacket_t *zclMSG);
static afIncomingMSGPacket_t buildZCLIncomingMSG(void *testData, uint8 endPoint, uint16 clusterID);

static SimpleDescriptionFormat_t zclTest_SimpleDesc =
{
  ZCL_TEST_ENDPOINT,                  	//  int Endpoint;
  ZCL_HA_PROFILE_ID,                    //  uint16 AppProfId;
  ZCL_HA_DEVICEID_ON_OFF_SWITCH,        //  uint16 AppDeviceId;
  TEST_DEVICE_VERSION,            		//  int   AppDevVer:4;
  TEST_FLAGS,                     		//  int   AppFlags:4;
  ZCLTEST_MAX_INCLUSTERS,         		//  byte  AppNumInClusters;
  (cId_t *)zclTest_InClusterList, 		//  byte *pAppInClusterList;
  ZCLTEST_MAX_OUTCLUSTERS,        		//  byte  AppNumInClusters;
  (cId_t *)zclTest_OutClusterList 		//  byte *pAppInClusterList;
};

static afAddrType_t testSrcAddr;

const pTaskEventHandlerFn tasksArr[] = {
  macEventLoop,
  nwk_event_loop,
  Hal_ProcessEvent,
  APS_event_loop,
  ZDApp_event_loop,
  zcl_event_loop,
  bdb_event_loop,
  zclGenericApp_event_loop
};

const uint8 tasksCnt = sizeof( tasksArr ) / sizeof( tasksArr[0] );
uint16 *tasksEvents;
/*******************************************/

int main()
{
  uint8 status = NULL;
  uint8 *testData;
  
  osal_int_disable( INTS_ALL );
  osal_mem_init();
  osal_int_enable( INTS_ALL );
  initialization();
  
  // Read seed file
  FILE *fp = fopen(seedfile,"rb");
  if(fp == NULL)
    return 1;
  
  long lSize;
  fseek(fp,0,SEEK_END);
  lSize = ftell(fp);
  rewind(fp);
  testData = (uint8 *)osal_mem_alloc(sizeof(uint8)*lSize);
  fread(testData,1,lSize,fp);
  fclose(fp);

  /********************************************
   *
   * System Configuration - Randomly set system with different configurations
   *
   ********************************************/
  uint8 testEndPoint = ZCL_TEST_ENDPOINT;
  uint8 testClusterID = ZCL_CLUSTER_ID_GEN_BASIC;
  srand(time(0));
  int config_rand = rand() % 10;
  if (config_rand == 0) {
	testEndPoint = OTA_TEST_ENDPOINT;
	testClusterID = ZCL_CLUSTER_ID_GEN_IDENTIFY;
  }
  else if(config_rand == 1) {
	testClusterID = ZCL_CLUSTER_ID_GEN_IDENTIFY;
  }
  printf("Setup configuration%d.\r\n",config_rand);
  CONST uint8 zclTestCmdsArraySize = ( sizeof(zclTest_Cmds_Basic) / sizeof(zclTest_Cmds_Basic[0]) );
  CONST uint8 zclTest_NumAttributes = ( sizeof(zclTest_Attrs_All) / sizeof(zclTest_Attrs_All[0]) );
  CONST uint8 otaTestCmdsArraySize = ( sizeof(otaTest_Cmds_Basic) / sizeof(otaTest_Cmds_Basic[0]) );
  CONST uint8 otaTest_NumAttributes = ( sizeof(otaTest_Attrs_Basic) / sizeof(otaTest_Attrs_Basic[0]) );
  zcl_registerForMsg(ZCLTestID);
  zcl_registerForMsgExt(ZCLTestID, OTA_TEST_ENDPOINT);
  zcl_registerForMsgExt(ZCLTestID, ZCL_TEST_ENDPOINT);
  zcl_registerAttrList(OTA_TEST_ENDPOINT,otaTest_NumAttributes, otaTest_Attrs_Basic);
  zcl_registerAttrList(ZCL_TEST_ENDPOINT,zclTest_NumAttributes, zclTest_Attrs_All);
  zcl_registerCmdList(OTA_TEST_ENDPOINT,otaTestCmdsArraySize, otaTest_Cmds_Basic);
  zcl_registerCmdList(ZCL_TEST_ENDPOINT,zclTestCmdsArraySize, zclTest_Cmds_Basic);
  zcl_registerClusterOptionList(ZCL_TEST_ENDPOINT, TEST_MAX_OPTIONS, zclBasic_Test_Options);
  zcl_registerClusterOptionList(OTA_TEST_ENDPOINT, TEST_MAX_OPTIONS, zclOta_Test_Options);
  zcl_registerReadWriteCB(ZCL_TEST_ENDPOINT, zclReadWriteCB, NULL);
  
  afIncomingMSGPacket_t zclMSG = buildZCLIncomingMSG(testData, testEndPoint, testClusterID);
  status = (uint8)zcl_ProcessMessageMSG(&zclMSG);
  printf("Test Status of zcl_ProcessMessageMSG:0x%02X\n\n",status);
  process_no_caller_funcs(&zclMSG);
  return 0;
}

static void initSourceEP(void)
{
  endPointDesc_t *epDesc = osal_mem_alloc( sizeof ( endPointDesc_t ) );
  if ( epDesc )
  {
    // Fill out the endpoint description.
    epDesc->endPoint = ZCL_TEST_ENDPOINT;
    epDesc->task_id = (uint8 *)ZCLTestID; 
    epDesc->simpleDesc = &zclTest_SimpleDesc;
    epDesc->latencyReq = noLatencyReqs;

    // Register the endpoint description with the AF
    afRegister( epDesc );
  }
}

static void initDestAddr(void)
{
  testSrcAddr.addrMode = (afAddrMode_t)AddrBroadcast;
  testSrcAddr.endPoint = ZCL_TEST_ENDPOINT;
  testSrcAddr.addr.shortAddr = 0xFFFC;
}

static void initialization()
{
  tasksEvents = (uint16 *)osal_mem_alloc( sizeof( uint16 ) * tasksCnt);
  osal_memset( tasksEvents, 0, (sizeof( uint16 ) * tasksCnt));
  initDestAddr();
  initSourceEP();
}

static afIncomingMSGPacket_t buildZCLIncomingMSG(void *testData, uint8 endPoint, uint16 clusterID) {
  afIncomingMSGPacket_t afMsg;
  afMsg.hdr.event = ZCL_INCOMING_MSG;
  afMsg.endPoint = endPoint;
  afMsg.srcAddr = testSrcAddr;
  afMsg.wasBroadcast = FALSE;
  afMsg.groupId = 0;
  afMsg.macDestAddr = 0x4F49;
  afMsg.clusterId = clusterID;
  afMsg.cmd.TransSeqNumber = zclTestSeq++;
  
  char pData[strlen(testData)];
  int data_len = 0;
  int frame_control = 0;

  char *data_token = strtok(testData, " ");
  while(data_token != NULL){  // Parse Message
    if (data_len == 0) {
	frame_control = strtol(data_token, NULL, 10);
        pData[data_len] = (uint8)frame_control;
        data_len++;	
    }
    else if(((frame_control & ZCL_FRAME_CONTROL_MANU_SPECIFIC) == 4 && data_len < 5)|| ((frame_control & ZCL_FRAME_CONTROL_MANU_SPECIFIC) != 4 && data_len < 3)) {
	pData[data_len] = (uint8)strtol(data_token, NULL, 10);
        data_len++;
    }
    else {
      if(strlen(data_token)==1){
        if(isdigit(data_token[0]))
          pData[data_len] = (uint8)strtol(data_token, NULL, 10);
        else
          pData[data_len] = (uint8)data_token[0];
        data_len++;
      }
      else {
        int printable = 1;
        for(int i = 0;i < strlen(data_token);i++) {
          if(!isprint(data_token[i])) {
            printable = 0;
            break;
          }
	}
        if(printable){
          pData[data_len] = (uint8)strtol(data_token, NULL, 10);
          data_len++;
        }
      }
    }
    
    data_token = strtok(NULL, " ");
  }
  afMsg.cmd.DataLength = (uint16)data_len;
  afMsg.cmd.Data = (uint8 *)&pData;
  return afMsg;
}

static ZStatus_t zclReadWriteCB( uint16 clusterId, uint16 attrId, uint8 oper, uint8 *pValue, uint16 *pLen ) {
	int stat = rand() % 10;
	if(stat > 3){
		return ZCL_STATUS_SUCCESS;
	} else {
		return ZCL_STATUS_READ_ONLY;   
	}
}

static void process_no_caller_funcs(afIncomingMSGPacket_t *zclMSG){
  printf("Call %s\n", __func__);
  uint8 status = NULL;
  zclIncoming_t inMsg;
  inMsg.msg = zclMSG;
  inMsg.attrCmd = NULL;
  inMsg.pData = NULL;
  inMsg.pDataLen = 0;

  inMsg.pData = zclParseHdr( &(inMsg.hdr), zclMSG->cmd.Data );
  inMsg.pDataLen = zclMSG->cmd.DataLength;
  inMsg.pDataLen -= (uint16)(inMsg.pData - zclMSG->cmd.Data);
  
  zclParseCmd_t parseCmd;
  parseCmd.endpoint = zclMSG->endPoint;
  parseCmd.dataLen = inMsg.pDataLen;
  parseCmd.pData = inMsg.pData;
  
  if(inMsg.hdr.commandID == ZCL_CMD_CONFIG_REPORT){
	// Call zcl_SendConfigReportCmd 0x06
	inMsg.attrCmd = (zclCfgReportCmd_t *)zclParseInConfigReportCmd(&parseCmd);
	status = zcl_SendConfigReportCmd(inMsg.msg->endPoint,&(inMsg.msg->srcAddr),inMsg.msg->clusterId,
			inMsg.attrCmd,inMsg.hdr.fc.direction,inMsg.hdr.fc.disableDefaultRsp,inMsg.msg->cmd.TransSeqNumber);
	printf("Test Status of zcl_SendConfigReportCmd:0x%02X\n",status);
  }
  else if(inMsg.hdr.commandID == ZCL_CMD_READ_REPORT_CFG_RSP){
	// Call zcl_SendReadReportCfgCmd 0x09
	inMsg.attrCmd = (zclReadReportCfgCmd_t *)zclParseInReadReportCfgCmd(&parseCmd);
	status = zcl_SendReadReportCfgCmd(inMsg.msg->endPoint,&(inMsg.msg->srcAddr),inMsg.msg->clusterId,
			inMsg.attrCmd,inMsg.hdr.fc.direction,inMsg.hdr.fc.disableDefaultRsp,inMsg.msg->cmd.TransSeqNumber);
	printf("Test Status of zcl_SendReadReportCfgCmd:0x%02X\n",status);
  }
  else if(inMsg.hdr.commandID == ZCL_CMD_REPORT){
	// Call zcl_SendReportCmd 0x0a
	inMsg.attrCmd = (zclReportCmd_t *)zclParseInReportCmd(&parseCmd);
	status = zcl_SendReportCmd(inMsg.msg->endPoint,&(inMsg.msg->srcAddr),inMsg.msg->clusterId,
			inMsg.attrCmd,inMsg.hdr.fc.direction,inMsg.hdr.fc.disableDefaultRsp,inMsg.msg->cmd.TransSeqNumber);
	printf("Test Status of zcl_SendReportCmd:0x%02X\n",status);
  }
  else if(inMsg.hdr.commandID == ZCL_CMD_DISCOVER_CMDS_RECEIVED || inMsg.hdr.commandID == ZCL_CMD_DISCOVER_CMDS_GEN){
	// Call zcl_SendDiscoverCmdsCmd 0x11 or 0x13
	inMsg.attrCmd = (zclDiscoverCmdsCmd_t *)zclParseInDiscCmdsCmd(&parseCmd);
	status = zcl_SendDiscoverCmdsCmd(inMsg.msg->endPoint,&(inMsg.msg->srcAddr),inMsg.msg->clusterId,inMsg.hdr.commandID,
			inMsg.attrCmd,inMsg.hdr.fc.direction,inMsg.hdr.fc.disableDefaultRsp,inMsg.msg->cmd.TransSeqNumber);
	printf("Test Status of zcl_SendDiscoverCmdsCmd:0x%02X\n",status);
  }
  else if(inMsg.hdr.commandID == ZCL_CMD_DISCOVER_ATTRS){
	// Call zcl_SendDiscoverAttrsCmd 0x0c
	inMsg.attrCmd = (zclDiscoverAttrsCmd_t *)zclParseInDiscAttrsCmd(&parseCmd);
	status = zcl_SendDiscoverAttrsCmd(inMsg.msg->endPoint,&(inMsg.msg->srcAddr),inMsg.msg->clusterId,
			inMsg.attrCmd,inMsg.hdr.fc.direction,inMsg.hdr.fc.disableDefaultRsp,inMsg.msg->cmd.TransSeqNumber);
	printf("Test Status of zcl_SendDiscoverAttrsCmd:0x%02X\n",status);
  }
}

