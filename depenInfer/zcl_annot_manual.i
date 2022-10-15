#line 1 "F:\\Workspace\\zigbfuzz\\depenInfer/zcl.c"
/**************************************************************************************************
  Filename:       zcl.c
  Revised:        $Date: 2015-09-09 11:51:49 -0700 (Wed, 09 Sep 2015) $
  Revision:       $Revision: 44489 $

  Description:    This file contains the Zigbee Cluster Library Foundation functions.


  Copyright 2006-2015 Texas Instruments Incorporated. All rights reserved.

  IMPORTANT: Your use of this Software is limited to those specific rights
  granted under the terms of a software license agreement between the user
  who downloaded the software, his/her employer (which must be your employer)
  and Texas Instruments Incorporated (the "License").  You may not use this
  Software unless you agree to abide by the terms of the License. The License
  limits your use, and you acknowledge, that the Software may not be modified,
  copied or distributed unless embedded on a Texas Instruments microcontroller
  or used solely and exclusively in conjunction with a Texas Instruments radio
  frequency transceiver, which is integrated into your product.  Other than for
  the foregoing purpose, you may not use, reproduce, copy, prepare derivative
  works of, modify, distribute, perform, display or sell this Software and/or
  its documentation for any purpose.

  YOU FURTHER ACKNOWLEDGE AND AGREE THAT THE SOFTWARE AND DOCUMENTATION ARE
  PROVIDED "AS IS" WITHOUT WARRANTY OF ANY KIND, EITHER EXPRESS OR IMPLIED,
  INCLUDING WITHOUT LIMITATION, ANY WARRANTY OF MERCHANTABILITY, TITLE,
  NON-INFRINGEMENT AND FITNESS FOR A PARTICULAR PURPOSE. IN NO EVENT SHALL
  TEXAS INSTRUMENTS OR ITS LICENSORS BE LIABLE OR OBLIGATED UNDER CONTRACT,
  NEGLIGENCE, STRICT LIABILITY, CONTRIBUTION, BREACH OF WARRANTY, OR OTHER
  LEGAL EQUITABLE THEORY ANY DIRECT OR INDIRECT DAMAGES OR EXPENSES
  INCLUDING BUT NOT LIMITED TO ANY INCIDENTAL, SPECIAL, INDIRECT, PUNITIVE
  OR CONSEQUENTIAL DAMAGES, LOST PROFITS OR LOST DATA, COST OF PROCUREMENT
  OF SUBSTITUTE GOODS, TECHNOLOGY, SERVICES, OR ANY CLAIMS BY THIRD PARTIES
  (INCLUDING BUT NOT LIMITED TO ANY DEFENSE THEREOF), OR OTHER SIMILAR COSTS.

  Should you have any questions regarding your right to use this Software,
  contact Texas Instruments Incorporated at www.TI.com.
**************************************************************************************************/

/*********************************************************************
 * INCLUDES
 */
#line 1 "F:\\Workspace\\zstack_iar_zf\\Components\\osal\\include\\ZComDef.h"
/**************************************************************************************************
  Filename:       ZComDef.h
  Revised:        $Date: 2014-11-24 23:50:22 -0800 (Mon, 24 Nov 2014) $
  Revision:       $Revision: 41235 $

  Description:    Type definitions and macros.


  Copyright 2004-2014 Texas Instruments Incorporated. All rights reserved.

  IMPORTANT: Your use of this Software is limited to those specific rights
  granted under the terms of a software license agreement between the user
  who downloaded the software, his/her employer (which must be your employer)
  and Texas Instruments Incorporated (the "License"). You may not use this
  Software unless you agree to abide by the terms of the License. The License
  limits your use, and you acknowledge, that the Software may not be modified,
  copied or distributed unless embedded on a Texas Instruments microcontroller
  or used solely and exclusively in conjunction with a Texas Instruments radio
  frequency transceiver, which is integrated into your product. Other than for
  the foregoing purpose, you may not use, reproduce, copy, prepare derivative
  works of, modify, distribute, perform, display or sell this Software and/or
  its documentation for any purpose.

  YOU FURTHER ACKNOWLEDGE AND AGREE THAT THE SOFTWARE AND DOCUMENTATION ARE
  PROVIDED "AS IS" WITHOUT WARRANTY OF ANY KIND, EITHER EXPRESS OR IMPLIED,
  INCLUDING WITHOUT LIMITATION, ANY WARRANTY OF MERCHANTABILITY, TITLE,
  NON-INFRINGEMENT AND FITNESS FOR A PARTICULAR PURPOSE. IN NO EVENT SHALL
  TEXAS INSTRUMENTS OR ITS LICENSORS BE LIABLE OR OBLIGATED UNDER CONTRACT,
  NEGLIGENCE, STRICT LIABILITY, CONTRIBUTION, BREACH OF WARRANTY, OR OTHER
  LEGAL EQUITABLE THEORY ANY DIRECT OR INDIRECT DAMAGES OR EXPENSES
  INCLUDING BUT NOT LIMITED TO ANY INCIDENTAL, SPECIAL, INDIRECT, PUNITIVE
  OR CONSEQUENTIAL DAMAGES, LOST PROFITS OR LOST DATA, COST OF PROCUREMENT
  OF SUBSTITUTE GOODS, TECHNOLOGY, SERVICES, OR ANY CLAIMS BY THIRD PARTIES
  (INCLUDING BUT NOT LIMITED TO ANY DEFENSE THEREOF), OR OTHER SIMILAR COSTS.

  Should you have any questions regarding your right to use this Software,
  contact Texas Instruments Incorporated at www.TI.com.
**************************************************************************************************/










/*********************************************************************
 * INCLUDES
 */
#line 1 "F:\\Workspace\\zstack_iar_zf\\Components\\osal\\include\\comdef.h"
/**************************************************************************************************
  Filename:       comdef.h
  Revised:        $Date: 2010-07-28 08:42:48 -0700 (Wed, 28 Jul 2010) $
  Revision:       $Revision: 23160 $

  Description:    Type definitions and macros.


  Copyright 2004-2008 Texas Instruments Incorporated. All rights reserved.

  IMPORTANT: Your use of this Software is limited to those specific rights
  granted under the terms of a software license agreement between the user
  who downloaded the software, his/her employer (which must be your employer)
  and Texas Instruments Incorporated (the "License").  You may not use this
  Software unless you agree to abide by the terms of the License. The License
  limits your use, and you acknowledge, that the Software may not be modified,
  copied or distributed unless embedded on a Texas Instruments microcontroller
  or used solely and exclusively in conjunction with a Texas Instruments radio
  frequency transceiver, which is integrated into your product.  Other than for
  the foregoing purpose, you may not use, reproduce, copy, prepare derivative
  works of, modify, distribute, perform, display or sell this Software and/or
  its documentation for any purpose.

  YOU FURTHER ACKNOWLEDGE AND AGREE THAT THE SOFTWARE AND DOCUMENTATION ARE
  PROVIDED “AS IS” WITHOUT WARRANTY OF ANY KIND, EITHER EXPRESS OR IMPLIED,
  INCLUDING WITHOUT LIMITATION, ANY WARRANTY OF MERCHANTABILITY, TITLE,
  NON-INFRINGEMENT AND FITNESS FOR A PARTICULAR PURPOSE. IN NO EVENT SHALL
  TEXAS INSTRUMENTS OR ITS LICENSORS BE LIABLE OR OBLIGATED UNDER CONTRACT,
  NEGLIGENCE, STRICT LIABILITY, CONTRIBUTION, BREACH OF WARRANTY, OR OTHER
  LEGAL EQUITABLE THEORY ANY DIRECT OR INDIRECT DAMAGES OR EXPENSES
  INCLUDING BUT NOT LIMITED TO ANY INCIDENTAL, SPECIAL, INDIRECT, PUNITIVE
  OR CONSEQUENTIAL DAMAGES, LOST PROFITS OR LOST DATA, COST OF PROCUREMENT
  OF SUBSTITUTE GOODS, TECHNOLOGY, SERVICES, OR ANY CLAIMS BY THIRD PARTIES
  (INCLUDING BUT NOT LIMITED TO ANY DEFENSE THEREOF), OR OTHER SIMILAR COSTS.

  Should you have any questions regarding your right to use this Software,
  contact Texas Instruments Incorporated at www.TI.com.
**************************************************************************************************/










/*********************************************************************
 * INCLUDES
 */

/* HAL */
#line 1 "F:\\Workspace\\zstack_iar_zf\\Components\\hal\\target\\CC2538\\hal_types.h"
/**************************************************************************************************
  Filename:       hal_types.h
  Revised:        $Date: 2013-05-17 11:25:11 -0700 (Fri, 17 May 2013) $
  Revision:       $Revision: 34355 $

  Description:    Describe the purpose and contents of the file.


  Copyright 2006-2013 Texas Instruments Incorporated. All rights reserved.

  IMPORTANT: Your use of this Software is limited to those specific rights
  granted under the terms of a software license agreement between the user
  who downloaded the software, his/her employer (which must be your employer)
  and Texas Instruments Incorporated (the "License").  You may not use this
  Software unless you agree to abide by the terms of the License. The License
  limits your use, and you acknowledge, that the Software may not be modified,
  copied or distributed unless embedded on a Texas Instruments microcontroller
  or used solely and exclusively in conjunction with a Texas Instruments radio
  frequency transceiver, which is integrated into your product.  Other than for
  the foregoing purpose, you may not use, reproduce, copy, prepare derivative
  works of, modify, distribute, perform, display or sell this Software and/or
  its documentation for any purpose.

  YOU FURTHER ACKNOWLEDGE AND AGREE THAT THE SOFTWARE AND DOCUMENTATION ARE
  PROVIDED “AS IS” WITHOUT WARRANTY OF ANY KIND, EITHER EXPRESS OR IMPLIED,
  INCLUDING WITHOUT LIMITATION, ANY WARRANTY OF MERCHANTABILITY, TITLE,
  NON-INFRINGEMENT AND FITNESS FOR A PARTICULAR PURPOSE. IN NO EVENT SHALL
  TEXAS INSTRUMENTS OR ITS LICENSORS BE LIABLE OR OBLIGATED UNDER CONTRACT,
  NEGLIGENCE, STRICT LIABILITY, CONTRIBUTION, BREACH OF WARRANTY, OR OTHER
  LEGAL EQUITABLE THEORY ANY DIRECT OR INDIRECT DAMAGES OR EXPENSES
  INCLUDING BUT NOT LIMITED TO ANY INCIDENTAL, SPECIAL, INDIRECT, PUNITIVE
  OR CONSEQUENTIAL DAMAGES, LOST PROFITS OR LOST DATA, COST OF PROCUREMENT
  OF SUBSTITUTE GOODS, TECHNOLOGY, SERVICES, OR ANY CLAIMS BY THIRD PARTIES
  (INCLUDING BUT NOT LIMITED TO ANY DEFENSE THEREOF), OR OTHER SIMILAR COSTS.

  Should you have any questions regarding your right to use this Software,
  contact Texas Instruments Incorporated at www.TI.com.
**************************************************************************************************/





/* ------------------------------------------------------------------------------------------------
 *                                               Types
 * ------------------------------------------------------------------------------------------------
 */
typedef signed   char      int8;
typedef unsigned char      uint8;

typedef signed   short     int16;
typedef unsigned short     uint16;

typedef signed   long      int32;
typedef unsigned long      uint32;
typedef unsigned long long uint64; 
typedef uint32             halDataAlign_t;



/* ------------------------------------------------------------------------------------------------
 *                                          Compiler Macros
 * ------------------------------------------------------------------------------------------------
 */
/* ----------- IAR Compiler ----------- */



/* ----------- KEIL Compiler ---------- */
#line 89 "F:\\Workspace\\zstack_iar_zf\\Components\\hal\\target\\CC2538\\hal_types.h"


/* ------------------------------------------------------------------------------------------------
 *                                        Standard Defines
 * ------------------------------------------------------------------------------------------------
 */













/* ------------------------------------------------------------------------------------------------
 *                                       Memory Attributes
 * ------------------------------------------------------------------------------------------------
 */





/**************************************************************************************************
 */
#line 55 "F:\\Workspace\\zstack_iar_zf\\Components\\osal\\include\\comdef.h"
#line 1 "F:\\Workspace\\zstack_iar_zf\\Components\\hal\\include\\hal_defs.h"
/**************************************************************************************************
  Filename:       hal_defs.h
  Revised:        $Date: 2014-11-19 13:29:24 -0800 (Wed, 19 Nov 2014) $
  Revision:       $Revision: 41175 $

  Description:    This file contains useful macros and data types


  Copyright 2005-2014 Texas Instruments Incorporated. All rights reserved.

  IMPORTANT: Your use of this Software is limited to those specific rights
  granted under the terms of a software license agreement between the user
  who downloaded the software, his/her employer (which must be your employer)
  and Texas Instruments Incorporated (the "License"). You may not use this
  Software unless you agree to abide by the terms of the License. The License
  limits your use, and you acknowledge, that the Software may not be modified,
  copied or distributed unless embedded on a Texas Instruments microcontroller
  or used solely and exclusively in conjunction with a Texas Instruments radio
  frequency transceiver, which is integrated into your product. Other than for
  the foregoing purpose, you may not use, reproduce, copy, prepare derivative
  works of, modify, distribute, perform, display or sell this Software and/or
  its documentation for any purpose.

  YOU FURTHER ACKNOWLEDGE AND AGREE THAT THE SOFTWARE AND DOCUMENTATION ARE
  PROVIDED “AS IS” WITHOUT WARRANTY OF ANY KIND, EITHER EXPRESS OR IMPLIED,
  INCLUDING WITHOUT LIMITATION, ANY WARRANTY OF MERCHANTABILITY, TITLE,
  NON-INFRINGEMENT AND FITNESS FOR A PARTICULAR PURPOSE. IN NO EVENT SHALL
  TEXAS INSTRUMENTS OR ITS LICENSORS BE LIABLE OR OBLIGATED UNDER CONTRACT,
  NEGLIGENCE, STRICT LIABILITY, CONTRIBUTION, BREACH OF WARRANTY, OR OTHER
  LEGAL EQUITABLE THEORY ANY DIRECT OR INDIRECT DAMAGES OR EXPENSES
  INCLUDING BUT NOT LIMITED TO ANY INCIDENTAL, SPECIAL, INDIRECT, PUNITIVE
  OR CONSEQUENTIAL DAMAGES, LOST PROFITS OR LOST DATA, COST OF PROCUREMENT
  OF SUBSTITUTE GOODS, TECHNOLOGY, SERVICES, OR ANY CLAIMS BY THIRD PARTIES
  (INCLUDING BUT NOT LIMITED TO ANY DEFENSE THEREOF), OR OTHER SIMILAR COSTS.

  Should you have any questions regarding your right to use this Software,
  contact Texas Instruments Incorporated at www.TI.com.
**************************************************************************************************/





/* ------------------------------------------------------------------------------------------------
 *                                             Macros
 * ------------------------------------------------------------------------------------------------
 */






















/* takes a byte out of a uint32 : var - uint32,  ByteNum - byte to take out (0 - 3) */





















// Write the 32bit value of 'val' in little endian format to the buffer pointed 
// to by pBuf, and increment pBuf by 4
#line 101 "F:\\Workspace\\zstack_iar_zf\\Components\\hal\\include\\hal_defs.h"

// Return the 32bit little-endian formatted value pointed to by pBuf, and increment pBuf by 4


#line 117 "F:\\Workspace\\zstack_iar_zf\\Components\\hal\\include\\hal_defs.h"

/*
 *  This macro is for use by other macros to form a fully valid C statement.
 *  Without this, the if/else conditionals could show unexpected behavior.
 *
 *  For example, use...
 *    #define SET_REGS()  st( ioreg1 = 0; ioreg2 = 0; )
 *  instead of ...
 *    #define SET_REGS()  { ioreg1 = 0; ioreg2 = 0; }
 *  or
 *    #define  SET_REGS()    ioreg1 = 0; ioreg2 = 0;
 *  The last macro would not behave as expected in the if/else construct.
 *  The second to last macro will cause a compiler error in certain uses
 *  of if/else construct
 *
 *  It is not necessary, or recommended, to use this macro where there is
 *  already a valid C statement.  For example, the following is redundant...
 *    #define CALL_FUNC()   st(  func();  )
 *  This should simply be...
 *    #define CALL_FUNC()   func()
 *
 * (The while condition below evaluates false without generating a
 *  constant-controlling-loop type of warning on most compilers.)
 */



/**************************************************************************************************
 */
#line 56 "F:\\Workspace\\zstack_iar_zf\\Components\\osal\\include\\comdef.h"

/*********************************************************************
 * Lint Keywords
 */


#line 71 "F:\\Workspace\\zstack_iar_zf\\Components\\osal\\include\\comdef.h"

/*********************************************************************
 * CONSTANTS
 */

















/*** Generic Status Return Values ***/
#line 107 "F:\\Workspace\\zstack_iar_zf\\Components\\osal\\include\\comdef.h"

/*** NV Error Mask ***/
#line 115 "F:\\Workspace\\zstack_iar_zf\\Components\\osal\\include\\comdef.h"
  
/*********************************************************************
 * TYPEDEFS
 */

// Generic Status return
typedef uint8 Status_t;

// Data types
typedef int32   int24;
typedef uint32  uint24;

/*********************************************************************
 * Global System Events
 */



/*********************************************************************
 * Global Generic System Messages
 */



// OSAL System Message IDs/Events Reserved for applications (user applications)
// 0xE0 – 0xFC

/*********************************************************************
 * MACROS
 */

/*********************************************************************
 * GLOBAL VARIABLES
 */

/*********************************************************************
 * FUNCTIONS
 */

/*********************************************************************
*********************************************************************/





#line 53 "F:\\Workspace\\zstack_iar_zf\\Components\\osal\\include\\ZComDef.h"
#line 1 "F:\\Workspace\\zstack_iar_zf\\Components\\services\\saddr\\saddr.h"
/**************************************************************************************************
  Filename:       saddr.h
  Revised:        $Date: 2009-12-10 08:32:15 -0800 (Thu, 10 Dec 2009) $
  Revision:       $Revision: 21311 $

  Description:    Zigbee and 802.15.4 device address utility functions.


  Copyright 2005-2010 Texas Instruments Incorporated. All rights reserved.

  IMPORTANT: Your use of this Software is limited to those specific rights
  granted under the terms of a software license agreement between the user
  who downloaded the software, his/her employer (which must be your employer)
  and Texas Instruments Incorporated (the "License").  You may not use this
  Software unless you agree to abide by the terms of the License. The License
  limits your use, and you acknowledge, that the Software may not be modified,
  copied or distributed unless embedded on a Texas Instruments microcontroller
  or used solely and exclusively in conjunction with a Texas Instruments radio
  frequency transceiver, which is integrated into your product.  Other than for
  the foregoing purpose, you may not use, reproduce, copy, prepare derivative
  works of, modify, distribute, perform, display or sell this Software and/or
  its documentation for any purpose.

  YOU FURTHER ACKNOWLEDGE AND AGREE THAT THE SOFTWARE AND DOCUMENTATION ARE
  PROVIDED “AS IS” WITHOUT WARRANTY OF ANY KIND, EITHER EXPRESS OR IMPLIED,
  INCLUDING WITHOUT LIMITATION, ANY WARRANTY OF MERCHANTABILITY, TITLE,
  NON-INFRINGEMENT AND FITNESS FOR A PARTICULAR PURPOSE. IN NO EVENT SHALL
  TEXAS INSTRUMENTS OR ITS LICENSORS BE LIABLE OR OBLIGATED UNDER CONTRACT,
  NEGLIGENCE, STRICT LIABILITY, CONTRIBUTION, BREACH OF WARRANTY, OR OTHER
  LEGAL EQUITABLE THEORY ANY DIRECT OR INDIRECT DAMAGES OR EXPENSES
  INCLUDING BUT NOT LIMITED TO ANY INCIDENTAL, SPECIAL, INDIRECT, PUNITIVE
  OR CONSEQUENTIAL DAMAGES, LOST PROFITS OR LOST DATA, COST OF PROCUREMENT
  OF SUBSTITUTE GOODS, TECHNOLOGY, SERVICES, OR ANY CLAIMS BY THIRD PARTIES
  (INCLUDING BUT NOT LIMITED TO ANY DEFENSE THEREOF), OR OTHER SIMILAR COSTS.

  Should you have any questions regarding your right to use this Software,
  contact Texas Instruments Incorporated at www.TI.com.
**************************************************************************************************/









/****************************************************************************
 * MACROS
 */

/* Extended address length */


/* Address modes */




/****************************************************************************
 * TYPEDEFS
 */

/* Extended address */
typedef uint8 sAddrExt_t[8];

/* Combined short/extended device address */
typedef struct
{
  union
  {
    uint16      shortAddr;    /* Short address */
    sAddrExt_t  extAddr;      /* Extended address */
  } addr;
  uint8         addrMode;     /* Address mode */
} sAddr_t;

/****************************************************************************
 * @fn          sAddrCmp
 *
 * @brief       Compare two device addresses.
 *
 * input parameters
 *
 * @param       pAddr1        - Pointer to first address.
 * @param       pAddr2        - Pointer to second address.
 *
 * output parameters
 *
 * @return      TRUE if addresses are equal, FALSE otherwise
 */
extern _Bool sAddrCmp(const sAddr_t *pAddr1, const sAddr_t *pAddr2);

/****************************************************************************
 * @fn          sAddrIden
 *
 * @brief       Check if two device addresses are identical.
 *
 *              This routine is virtually the same as sAddrCmp, which is used
 *              to determine if two different addresses are the same. However,
 *              this routine can be used to determine if an address is the
 *              same as a previously stored address. The key difference is in
 *              the former case, if the address mode is "none", then the
 *              assumption is that the two addresses can not be the same. But
 *              in the latter case, the address mode itself is being compared.
 *              So two addresses can be identical even if the address mode is
 *              "none", as long as the address mode of both addresses being
 *              compared is the "none".
 *
 * input parameters
 *
 * @param       pAddr1        - Pointer to first address.
 * @param       pAddr2        - Pointer to second address.
 *
 * output parameters
 *
 * @return      TRUE if addresses are identical, FALSE otherwise
 */
extern _Bool sAddrIden(const sAddr_t *pAddr1, const sAddr_t *pAddr2);

/****************************************************************************
 * @fn          sAddrCpy
 *
 * @brief       Copy a device address.
 *
 * input parameters
 *
 * @param       pSrc         - Pointer to address to copy.
 *
 * output parameters
 *
 * @param       pDest        - Pointer to address of copy.
 *
 * @return      None.
 */
extern void sAddrCpy(sAddr_t *pDest, const sAddr_t *pSrc);

/****************************************************************************
 * @fn          sAddrExtCmp
 *
 * @brief       Compare two extended addresses.
 *
 * input parameters
 *
 * @param       pAddr1        - Pointer to first address.
 * @param       pAddr2        - Pointer to second address.
 *
 * output parameters
 *
 * @return      TRUE if addresses are equal, FALSE otherwise
 */
extern _Bool sAddrExtCmp(const uint8 * pAddr1, const uint8 * pAddr2);

/****************************************************************************
 * @fn          sAddrExtCpy
 *
 * @brief       Copy an extended address.
 *
 * input parameters
 *
 * @param       pSrc         - Pointer to address to copy.
 *
 * output parameters
 *
 * @param       pDest        - Pointer to address of copy.
 *
 * @return      pDest + SADDR_EXT_LEN.
 */
void *sAddrExtCpy(uint8 * pDest, const uint8 * pSrc);





#line 54 "F:\\Workspace\\zstack_iar_zf\\Components\\osal\\include\\ZComDef.h"


/*********************************************************************
 * CONSTANTS
 */




/*********************************************************************
 * CONSTANTS
 */

// Build Device Types - Used during compilation
//   These are the types of devices to build
//   Bit masked into ZSTACK_DEVICE_BUILD




/*** Return Values ***/


/*** Component IDs ***/
#line 87 "F:\\Workspace\\zstack_iar_zf\\Components\\osal\\include\\ZComDef.h"




/* Temp CompIDs for testing */





// OSAL NV Item IDs





// OSAL NV item IDs





// NWK Layer NV item IDs
#line 131 "F:\\Workspace\\zstack_iar_zf\\Components\\osal\\include\\ZComDef.h"
                                       // 0x0035 used above for new 32 bit Poll Rate
#line 142 "F:\\Workspace\\zstack_iar_zf\\Components\\osal\\include\\ZComDef.h"

// APS Layer NV item IDs
#line 153 "F:\\Workspace\\zstack_iar_zf\\Components\\osal\\include\\ZComDef.h"







// System statistics and metrics NV ID


// Additional NWK Layer NV item IDs




  


  
// Security NV Item IDs
#line 181 "F:\\Workspace\\zstack_iar_zf\\Components\\osal\\include\\ZComDef.h"







//deprecated: TRUSTCENTER_ADDR (16-bit)   0x006E











   
// ZDO NV Item IDs
#line 211 "F:\\Workspace\\zstack_iar_zf\\Components\\osal\\include\\ZComDef.h"



// ZCL NV item IDs
#line 223 "F:\\Workspace\\zstack_iar_zf\\Components\\osal\\include\\ZComDef.h"

// Non-standard NV item IDs


// NV Items Reserved for Commissioning Cluster Startup Attribute Set (SAS):
// 0x00B1 - 0x00BF: Parameters related to APS and NWK layers
// 0x00C1 - 0x00CF: Parameters related to Security
// 0x00D1 - 0x00DF: Current key parameters
#line 238 "F:\\Workspace\\zstack_iar_zf\\Components\\osal\\include\\ZComDef.h"

#line 247 "F:\\Workspace\\zstack_iar_zf\\Components\\osal\\include\\ZComDef.h"





// NV Items Reserved for Trust Center Link Key Table entries
// 0x0101 - 0x01FF



  


   



// NV Items Reserved for APS Link Key Table entries
// 0x0201 - 0x02FF



// NV items used to duplicate system elements




// NV Items Reserved for Proxy Table entries
// 0x0310 - 0x033F  



// NV Items Reserved for applications (user applications)
// 0x0401 – 0x0FFF


// ZCD_NV_STARTUP_OPTION values
//   These are bit weighted - you can OR these together.
//   Setting one of these bits will set their associated NV items
//   to code initialized values.





//FrameCounter should be persistence across factory new resets, this should not 
//used as part of FN reset procedure. Set to reset the FrameCounter of all 
//Nwk Security Material






/*********************************************************************
 * TYPEDEFS
 */

/*** Data Types ***/
typedef uint8   byte;
typedef uint16  UINT16;
typedef int16   INT16;

enum
{
  AddrNotPresent = 0,
  AddrGroup = 1,
  Addr16Bit = 2,
  Addr64Bit = 3,
  AddrBroadcast = 15
};



typedef byte ZLongAddr_t[8];

typedef struct
{
  union
  {
    uint16      shortAddr;
    ZLongAddr_t extAddr;
  } addr;
  byte addrMode;
} zAddrType_t;

// Redefined Generic Status Return Values for code backwards compatibility




// ZStack status values must start at 0x10, after the generic status values (defined in comdef.h)














// OTA Status values






// APS status values
#line 372 "F:\\Workspace\\zstack_iar_zf\\Components\\osal\\include\\ZComDef.h"

	// Security status values







	// NWK status values
#line 395 "F:\\Workspace\\zstack_iar_zf\\Components\\osal\\include\\ZComDef.h"

	// MAC status values
#line 421 "F:\\Workspace\\zstack_iar_zf\\Components\\osal\\include\\ZComDef.h"

typedef Status_t ZStatus_t;

typedef struct
{
  uint8  txCounter;    // Counter of transmission success/failures
  uint8  txCost;       // Average of sending rssi values if link staus is enabled
                       // i.e. NWK_LINK_STATUS_PERIOD is defined as non zero
  uint8  rxLqi;        // average of received rssi values
                       // needs to be converted to link cost (1-7) before used
  uint8  inKeySeqNum;  // security key sequence number
  uint32 inFrmCntr;    // security frame counter..
  uint16 txFailure;    // higher values indicate more failures
} linkInfo_t;

/*********************************************************************
 * Global System Messages
 */

#line 446 "F:\\Workspace\\zstack_iar_zf\\Components\\osal\\include\\ZComDef.h"







//#define KEY_CHANGE                0xC0    // Key Events

#line 462 "F:\\Workspace\\zstack_iar_zf\\Components\\osal\\include\\ZComDef.h"

#line 469 "F:\\Workspace\\zstack_iar_zf\\Components\\osal\\include\\ZComDef.h"


// OSAL System Message IDs/Events Reserved for applications (user applications)
// 0xE0 – 0xFC

/*********************************************************************
 * GLOBAL VARIABLES
 */

/*********************************************************************
 * FUNCTIONS
 */

/*********************************************************************
*********************************************************************/





#line 44 "F:\\Workspace\\zigbfuzz\\depenInfer/zcl.c"
#line 1 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\af\\AF.h"
/**************************************************************************************************
  Filename:       AF.h
  Revised:        $Date: 2014-11-04 10:53:36 -0800 (Tue, 04 Nov 2014) $
  Revision:       $Revision: 40974 $

  Description:    This file contains the Application Framework definitions.


  Copyright 2004-2014 Texas Instruments Incorporated. All rights reserved.

  IMPORTANT: Your use of this Software is limited to those specific rights
  granted under the terms of a software license agreement between the user
  who downloaded the software, his/her employer (which must be your employer)
  and Texas Instruments Incorporated (the "License").  You may not use this
  Software unless you agree to abide by the terms of the License. The License
  limits your use, and you acknowledge, that the Software may not be modified,
  copied or distributed unless embedded on a Texas Instruments microcontroller
  or used solely and exclusively in conjunction with a Texas Instruments radio
  frequency transceiver, which is integrated into your product.  Other than for
  the foregoing purpose, you may not use, reproduce, copy, prepare derivative
  works of, modify, distribute, perform, display or sell this Software and/or
  its documentation for any purpose.

  YOU FURTHER ACKNOWLEDGE AND AGREE THAT THE SOFTWARE AND DOCUMENTATION ARE
  PROVIDED "AS IS" WITHOUT WARRANTY OF ANY KIND, EITHER EXPRESS OR IMPLIED,
  INCLUDING WITHOUT LIMITATION, ANY WARRANTY OF MERCHANTABILITY, TITLE,
  NON-INFRINGEMENT AND FITNESS FOR A PARTICULAR PURPOSE. IN NO EVENT SHALL
  TEXAS INSTRUMENTS OR ITS LICENSORS BE LIABLE OR OBLIGATED UNDER CONTRACT,
  NEGLIGENCE, STRICT LIABILITY, CONTRIBUTION, BREACH OF WARRANTY, OR OTHER
  LEGAL EQUITABLE THEORY ANY DIRECT OR INDIRECT DAMAGES OR EXPENSES
  INCLUDING BUT NOT LIMITED TO ANY INCIDENTAL, SPECIAL, INDIRECT, PUNITIVE
  OR CONSEQUENTIAL DAMAGES, LOST PROFITS OR LOST DATA, COST OF PROCUREMENT
  OF SUBSTITUTE GOODS, TECHNOLOGY, SERVICES, OR ANY CLAIMS BY THIRD PARTIES
  (INCLUDING BUT NOT LIMITED TO ANY DEFENSE THEREOF), OR OTHER SIMILAR COSTS.

  Should you have any questions regarding your right to use this Software,
  contact Texas Instruments Incorporated at www.TI.com.
**************************************************************************************************/








/*********************************************************************
 * INCLUDES
 */

#line 1 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\nwk\\nwk.h"
/**************************************************************************************************
  Filename:       nwk.h
  Revised:        $Date: 2014-12-01 14:58:34 -0800 (Mon, 01 Dec 2014) $
  Revision:       $Revision: 41287 $

  Description:    Network layer logic component interface.


  Copyright 2004-2014 Texas Instruments Incorporated. All rights reserved.

  IMPORTANT: Your use of this Software is limited to those specific rights
  granted under the terms of a software license agreement between the user
  who downloaded the software, his/her employer (which must be your employer)
  and Texas Instruments Incorporated (the "License").  You may not use this
  Software unless you agree to abide by the terms of the License. The License
  limits your use, and you acknowledge, that the Software may not be modified,
  copied or distributed unless embedded on a Texas Instruments microcontroller
  or used solely and exclusively in conjunction with a Texas Instruments radio
  frequency transceiver, which is integrated into your product.  Other than for
  the foregoing purpose, you may not use, reproduce, copy, prepare derivative
  works of, modify, distribute, perform, display or sell this Software and/or
  its documentation for any purpose.

  YOU FURTHER ACKNOWLEDGE AND AGREE THAT THE SOFTWARE AND DOCUMENTATION ARE
  PROVIDED "AS IS" WITHOUT WARRANTY OF ANY KIND, EITHER EXPRESS OR IMPLIED,
  INCLUDING WITHOUT LIMITATION, ANY WARRANTY OF MERCHANTABILITY, TITLE,
  NON-INFRINGEMENT AND FITNESS FOR A PARTICULAR PURPOSE. IN NO EVENT SHALL
  TEXAS INSTRUMENTS OR ITS LICENSORS BE LIABLE OR OBLIGATED UNDER CONTRACT,
  NEGLIGENCE, STRICT LIABILITY, CONTRIBUTION, BREACH OF WARRANTY, OR OTHER
  LEGAL EQUITABLE THEORY ANY DIRECT OR INDIRECT DAMAGES OR EXPENSES
  INCLUDING BUT NOT LIMITED TO ANY INCIDENTAL, SPECIAL, INDIRECT, PUNITIVE
  OR CONSEQUENTIAL DAMAGES, LOST PROFITS OR LOST DATA, COST OF PROCUREMENT
  OF SUBSTITUTE GOODS, TECHNOLOGY, SERVICES, OR ANY CLAIMS BY THIRD PARTIES
  (INCLUDING BUT NOT LIMITED TO ANY DEFENSE THEREOF), OR OTHER SIMILAR COSTS.

  Should you have any questions regarding your right to use this Software,
  contact Texas Instruments Incorporated at www.TI.com.
**************************************************************************************************/








/*********************************************************************
 * INCLUDES
 */

#line 1 "F:\\Workspace\\zstack_iar_zf\\Components\\zmac\\ZMAC.h"
/**************************************************************************************************
  Filename:       ZMAC.h
  Revised:        $Date: 2014-06-20 15:25:38 -0700 (Fri, 20 Jun 2014) $
  Revision:       $Revision: 39136 $

  Description:    This file contains the ZStack MAC Porting Layer.


  Copyright 2004-2013 Texas Instruments Incorporated. All rights reserved.

  IMPORTANT: Your use of this Software is limited to those specific rights
  granted under the terms of a software license agreement between the user
  who downloaded the software, his/her employer (which must be your employer)
  and Texas Instruments Incorporated (the "License").  You may not use this
  Software unless you agree to abide by the terms of the License. The License
  limits your use, and you acknowledge, that the Software may not be modified,
  copied or distributed unless embedded on a Texas Instruments microcontroller
  or used solely and exclusively in conjunction with a Texas Instruments radio
  frequency transceiver, which is integrated into your product.  Other than for
  the foregoing purpose, you may not use, reproduce, copy, prepare derivative
  works of, modify, distribute, perform, display or sell this Software and/or
  its documentation for any purpose.

  YOU FURTHER ACKNOWLEDGE AND AGREE THAT THE SOFTWARE AND DOCUMENTATION ARE
  PROVIDED "AS IS" WITHOUT WARRANTY OF ANY KIND, EITHER EXPRESS OR IMPLIED,
  INCLUDING WITHOUT LIMITATION, ANY WARRANTY OF MERCHANTABILITY, TITLE,
  NON-INFRINGEMENT AND FITNESS FOR A PARTICULAR PURPOSE. IN NO EVENT SHALL
  TEXAS INSTRUMENTS OR ITS LICENSORS BE LIABLE OR OBLIGATED UNDER CONTRACT,
  NEGLIGENCE, STRICT LIABILITY, CONTRIBUTION, BREACH OF WARRANTY, OR OTHER
  LEGAL EQUITABLE THEORY ANY DIRECT OR INDIRECT DAMAGES OR EXPENSES
  INCLUDING BUT NOT LIMITED TO ANY INCIDENTAL, SPECIAL, INDIRECT, PUNITIVE
  OR CONSEQUENTIAL DAMAGES, LOST PROFITS OR LOST DATA, COST OF PROCUREMENT
  OF SUBSTITUTE GOODS, TECHNOLOGY, SERVICES, OR ANY CLAIMS BY THIRD PARTIES
  (INCLUDING BUT NOT LIMITED TO ANY DEFENSE THEREOF), OR OTHER SIMILAR COSTS.

  Should you have any questions regarding your right to use this Software,
  contact Texas Instruments Incorporated at www.TI.com.
**************************************************************************************************/









/*********************************************************************
 * INCLUDES
 */

#line 1 "F:\\Workspace\\zstack_iar_zf\\Components\\zmac\\f8w\\zmac_internal.h"
/**************************************************************************************************
  Filename:       zmac_internal.h
  Revised:        $Date: 2014-07-07 17:47:52 -0700 (Mon, 07 Jul 2014) $
  Revision:       $Revision: 39365 $

  Description:    This file contains the ZStack MAC Porting Layer.


  Copyright 2005-2014 Texas Instruments Incorporated. All rights reserved.

  IMPORTANT: Your use of this Software is limited to those specific rights
  granted under the terms of a software license agreement between the user
  who downloaded the software, his/her employer (which must be your employer)
  and Texas Instruments Incorporated (the "License").  You may not use this
  Software unless you agree to abide by the terms of the License. The License
  limits your use, and you acknowledge, that the Software may not be modified,
  copied or distributed unless embedded on a Texas Instruments microcontroller
  or used solely and exclusively in conjunction with a Texas Instruments radio
  frequency transceiver, which is integrated into your product.  Other than for
  the foregoing purpose, you may not use, reproduce, copy, prepare derivative
  works of, modify, distribute, perform, display or sell this Software and/or
  its documentation for any purpose.

  YOU FURTHER ACKNOWLEDGE AND AGREE THAT THE SOFTWARE AND DOCUMENTATION ARE
  PROVIDED “AS IS” WITHOUT WARRANTY OF ANY KIND, EITHER EXPRESS OR IMPLIED, 
  INCLUDING WITHOUT LIMITATION, ANY WARRANTY OF MERCHANTABILITY, TITLE, 
  NON-INFRINGEMENT AND FITNESS FOR A PARTICULAR PURPOSE. IN NO EVENT SHALL
  TEXAS INSTRUMENTS OR ITS LICENSORS BE LIABLE OR OBLIGATED UNDER CONTRACT,
  NEGLIGENCE, STRICT LIABILITY, CONTRIBUTION, BREACH OF WARRANTY, OR OTHER
  LEGAL EQUITABLE THEORY ANY DIRECT OR INDIRECT DAMAGES OR EXPENSES
  INCLUDING BUT NOT LIMITED TO ANY INCIDENTAL, SPECIAL, INDIRECT, PUNITIVE
  OR CONSEQUENTIAL DAMAGES, LOST PROFITS OR LOST DATA, COST OF PROCUREMENT
  OF SUBSTITUTE GOODS, TECHNOLOGY, SERVICES, OR ANY CLAIMS BY THIRD PARTIES
  (INCLUDING BUT NOT LIMITED TO ANY DEFENSE THEREOF), OR OTHER SIMILAR COSTS.

  Should you have any questions regarding your right to use this Software,
  contact Texas Instruments Incorporated at www.TI.com. 
**************************************************************************************************/









/********************************************************************************************************
 *                                               INCLUDES
 ********************************************************************************************************/

#line 1 "F:\\Workspace\\zstack_iar_zf\\Components\\mac\\include\\mac_api.h"
/**************************************************************************************************
  Filename:       mac_api.h
  Revised:        $Date: 2014-11-06 11:03:55 -0800 (Thu, 06 Nov 2014) $
  Revision:       $Revision: 41021 $

  Description:    Public interface file for 802.15.4 MAC.


  Copyright 2005-2014 Texas Instruments Incorporated. All rights reserved.

  IMPORTANT: Your use of this Software is limited to those specific rights
  granted under the terms of a software license agreement between the user
  who downloaded the software, his/her employer (which must be your employer)
  and Texas Instruments Incorporated (the "License").  You may not use this
  Software unless you agree to abide by the terms of the License. The License
  limits your use, and you acknowledge, that the Software may not be modified,
  copied or distributed unless embedded on a Texas Instruments microcontroller
  or used solely and exclusively in conjunction with a Texas Instruments radio
  frequency transceiver, which is integrated into your product.  Other than for
  the foregoing purpose, you may not use, reproduce, copy, prepare derivative
  works of, modify, distribute, perform, display or sell this Software and/or
  its documentation for any purpose.

  YOU FURTHER ACKNOWLEDGE AND AGREE THAT THE SOFTWARE AND DOCUMENTATION ARE
  PROVIDED “AS IS” WITHOUT WARRANTY OF ANY KIND, EITHER EXPRESS OR IMPLIED,
  INCLUDING WITHOUT LIMITATION, ANY WARRANTY OF MERCHANTABILITY, TITLE,
  NON-INFRINGEMENT AND FITNESS FOR A PARTICULAR PURPOSE. IN NO EVENT SHALL
  TEXAS INSTRUMENTS OR ITS LICENSORS BE LIABLE OR OBLIGATED UNDER CONTRACT,
  NEGLIGENCE, STRICT LIABILITY, CONTRIBUTION, BREACH OF WARRANTY, OR OTHER
  LEGAL EQUITABLE THEORY ANY DIRECT OR INDIRECT DAMAGES OR EXPENSES
  INCLUDING BUT NOT LIMITED TO ANY INCIDENTAL, SPECIAL, INDIRECT, PUNITIVE
  OR CONSEQUENTIAL DAMAGES, LOST PROFITS OR LOST DATA, COST OF PROCUREMENT
  OF SUBSTITUTE GOODS, TECHNOLOGY, SERVICES, OR ANY CLAIMS BY THIRD PARTIES
  (INCLUDING BUT NOT LIMITED TO ANY DEFENSE THEREOF), OR OTHER SIMILAR COSTS.

  Should you have any questions regarding your right to use this Software,
  contact Texas Instruments Incorporated at www.TI.com.
**************************************************************************************************/








/* ------------------------------------------------------------------------------------------------
 *                                          Includes
 * ------------------------------------------------------------------------------------------------
 */
#line 1 "F:\\Workspace\\zstack_iar_zf\\Components\\services\\sdata\\sdata.h"
/**************************************************************************************************
  Filename:       sdata.h
  Revised:        $Date: 2007-10-28 18:41:49 -0700 (Sun, 28 Oct 2007) $
  Revision:       $Revision: 15799 $

  Description:    Data buffer service.


  Copyright 2005-2007 Texas Instruments Incorporated. All rights reserved.

  IMPORTANT: Your use of this Software is limited to those specific rights
  granted under the terms of a software license agreement between the user
  who downloaded the software, his/her employer (which must be your employer)
  and Texas Instruments Incorporated (the "License").  You may not use this
  Software unless you agree to abide by the terms of the License. The License
  limits your use, and you acknowledge, that the Software may not be modified,
  copied or distributed unless embedded on a Texas Instruments microcontroller
  or used solely and exclusively in conjunction with a Texas Instruments radio
  frequency transceiver, which is integrated into your product.  Other than for
  the foregoing purpose, you may not use, reproduce, copy, prepare derivative
  works of, modify, distribute, perform, display or sell this Software and/or
  its documentation for any purpose.

  YOU FURTHER ACKNOWLEDGE AND AGREE THAT THE SOFTWARE AND DOCUMENTATION ARE
  PROVIDED “AS IS” WITHOUT WARRANTY OF ANY KIND, EITHER EXPRESS OR IMPLIED, 
  INCLUDING WITHOUT LIMITATION, ANY WARRANTY OF MERCHANTABILITY, TITLE, 
  NON-INFRINGEMENT AND FITNESS FOR A PARTICULAR PURPOSE. IN NO EVENT SHALL
  TEXAS INSTRUMENTS OR ITS LICENSORS BE LIABLE OR OBLIGATED UNDER CONTRACT,
  NEGLIGENCE, STRICT LIABILITY, CONTRIBUTION, BREACH OF WARRANTY, OR OTHER
  LEGAL EQUITABLE THEORY ANY DIRECT OR INDIRECT DAMAGES OR EXPENSES
  INCLUDING BUT NOT LIMITED TO ANY INCIDENTAL, SPECIAL, INDIRECT, PUNITIVE
  OR CONSEQUENTIAL DAMAGES, LOST PROFITS OR LOST DATA, COST OF PROCUREMENT
  OF SUBSTITUTE GOODS, TECHNOLOGY, SERVICES, OR ANY CLAIMS BY THIRD PARTIES
  (INCLUDING BUT NOT LIMITED TO ANY DEFENSE THEREOF), OR OTHER SIMILAR COSTS.

  Should you have any questions regarding your right to use this Software,
  contact Texas Instruments Incorporated at www.TI.com. 
**************************************************************************************************/








/* ------------------------------------------------------------------------------------------------
 *                                           Typedefs
 * ------------------------------------------------------------------------------------------------
 */

typedef struct
{
  uint8     *p;
  uint8     len;
} sData_t;





#line 54 "F:\\Workspace\\zstack_iar_zf\\Components\\mac\\include\\mac_api.h"

/* ------------------------------------------------------------------------------------------------
 *                                           Constants
 * ------------------------------------------------------------------------------------------------
 */

/* Status */
#line 123 "F:\\Workspace\\zstack_iar_zf\\Components\\mac\\include\\mac_api.h"

/* MAC Security Level */
#line 133 "F:\\Workspace\\zstack_iar_zf\\Components\\mac\\include\\mac_api.h"

/* Key Identifier Mode */






/* Key identifier field length in bytes */





/* Key source maximum length in bytes */


/* Key index length in bytes */


/* Frame counter length in bytes */


/* Key length in bytes */


/* Key lookup data length in bytes */





/* Data constants */




#line 177 "F:\\Workspace\\zstack_iar_zf\\Components\\mac\\include\\mac_api.h"

/* MHR length for received frame */


/* TX Options */
#line 197 "F:\\Workspace\\zstack_iar_zf\\Components\\mac\\include\\mac_api.h"

/* Green Power limitations */


/* Channels */
#line 221 "F:\\Workspace\\zstack_iar_zf\\Components\\mac\\include\\mac_api.h"
  

  





  
/* This macro converts a channel to a mask */


/* Channel Masks */
#line 253 "F:\\Workspace\\zstack_iar_zf\\Components\\mac\\include\\mac_api.h"

/* Channel Page */



  
/* Capability Information */
#line 266 "F:\\Workspace\\zstack_iar_zf\\Components\\mac\\include\\mac_api.h"

/* Standard PIB Get and Set Attributes */
#line 319 "F:\\Workspace\\zstack_iar_zf\\Components\\mac\\include\\mac_api.h"

/* Security PIB Get and Set Attributes */
#line 330 "F:\\Workspace\\zstack_iar_zf\\Components\\mac\\include\\mac_api.h"

#line 340 "F:\\Workspace\\zstack_iar_zf\\Components\\mac\\include\\mac_api.h"

/* Proprietary Security PIB Get and Set Attributes */
#line 348 "F:\\Workspace\\zstack_iar_zf\\Components\\mac\\include\\mac_api.h"

/* Proprietary PIB Get and Set Attributes */
#line 361 "F:\\Workspace\\zstack_iar_zf\\Components\\mac\\include\\mac_api.h"

/* Diagnostic PIB Get and Set Attributes */
#line 371 "F:\\Workspace\\zstack_iar_zf\\Components\\mac\\include\\mac_api.h"




/* Disassociate Reason */




/* Scan Type */
#line 395 "F:\\Workspace\\zstack_iar_zf\\Components\\mac\\include\\mac_api.h"

/* Special address values */




/* Comm status indication reasons */




/* Power Mode */




/* MAC Callback Events */
#line 429 "F:\\Workspace\\zstack_iar_zf\\Components\\mac\\include\\mac_api.h"

/* The length of the random seed is set for maximum requirement which is
 * 32 for ZigBeeIP
 */


/* ------------------------------------------------------------------------------------------------
 *                                           Macros
 * ------------------------------------------------------------------------------------------------
 */

/* Returns the number of short addresses in the pending address specification */


/* Returns the number of extended addresses in the pending address specification */


/* Returns the length in bytes of the pending address fields in the beacon */



/* The following macros are provided to help parse the superframe specification */
#line 457 "F:\\Workspace\\zstack_iar_zf\\Components\\mac\\include\\mac_api.h"

/* ------------------------------------------------------------------------------------------------
 *                                           Typedefs
 * ------------------------------------------------------------------------------------------------
 */

/* MAC event header type */
typedef struct
{
  uint8   event;              /* MAC event */
  uint8   status;             /* MAC status */
} macEventHdr_t;

/* Common security type */
typedef struct
{
  uint8   keySource[8];  /* Key source */
  uint8   securityLevel;                      /* Security level */
  uint8   keyIdMode;                          /* Key identifier mode */
  uint8   keyIndex;                           /* Key index */
} macSec_t;

/* Key ID Lookup Descriptor */
typedef struct
{
  uint8              lookupData[9];  /* Data used to identify the key */
  uint8              lookupDataSize;  /* 0x00 indicates 5 octets; 0x01 indicates 9 octets. */
} keyIdLookupDescriptor_t;

/* Key Device Descriptor */
typedef struct
{
  uint8              deviceDescriptorHandle;  /* Handle to the DeviceDescriptor */
  _Bool               uniqueDevice;            /* Is it a link key or a group key? */
  _Bool               blackListed;             /* This key exhausted the frame counter. */
} keyDeviceDescriptor_t;

/* Key Usage Descriptor */
typedef struct
{
  uint8              frameType;               /* Frame Type */
  uint8              cmdFrameId;              /* Command Frame Identifier */
} keyUsageDescriptor_t;

/* Key Descriptor */
typedef struct
{
  keyIdLookupDescriptor_t  *keyIdLookupList;   /* A list identifying this KeyDescriptor */
  uint8                    keyIdLookupEntries; /* The number of entries in KeyIdLookupList */

  keyDeviceDescriptor_t    *keyDeviceList;        /* A list indicating which devices are
                                                     currently using this key, including
                                                     their blacklist status. */
  uint8                    keyDeviceListEntries;  /* The number of entries in KeyDeviceList */

  keyUsageDescriptor_t     *keyUsageList;         /* A list indicating which frame types
                                                   * this key may be used with. */
  uint8                    keyUsageListEntries;   /* The number of entries in KeyUsageList */

  uint8                    key[16];  /* The actual value of the key */
  uint32                   frameCounter;  /* PIB frame counter in 802.15.4 is universal across key,
                                           * but it makes more sense to associate a frame counter
                                           * with a key. */
} keyDescriptor_t;

/* Device Descriptor */
typedef struct
{
  uint16             panID;          /* The 16-bit PAN identifier of the device */
  uint16             shortAddress;   /* The 16-bit short address of the device */
  sAddrExt_t         extAddress;     /* The 64-bit IEEE extended address of the
                                        device. This element is also used in
                                        unsecuring operations on incoming frames. */

  uint32             frameCounter[2];
                                     /* The incoming frame counter of the device
                                        This value is used to ensure sequential
                                        freshness of frames. */
  _Bool               exempt;         /* Device may override the minimum security
                                        level settings. */
} deviceDescriptor_t;

/* Security Level Descriptor */
typedef struct
{
  uint8              frameType;              /* Frame Type */
  uint8              commandFrameIdentifier; /* Command Frame ID */
  uint8              securityMinimum;        /* The minimal required/expected security
                                                level for incoming MAC frames. */
  _Bool               securityOverrideSecurityMinimum;
                                             /* Indication of whether originating devices
                                                for which the Exempt flag is set may
                                                override the minimum security level
                                                indicated by the SecurityMinimum
                                                element. If TRUE, this indicates that for
                                                originating devices with Exempt status,
                                                the incoming security level zero is
                                                acceptable. */
} securityLevelDescriptor_t;

/* For internal use only */
typedef struct
{
  uint8                   key_index;
  uint8                   key_id_lookup_index;
  keyIdLookupDescriptor_t macKeyIdLookupEntry;
} macSecurityPibKeyIdLookupEntry_t;

typedef struct
{
  uint8                   key_index;
  uint8                   key_device_index;
  keyDeviceDescriptor_t   macKeyDeviceEntry;
} macSecurityPibKeyDeviceEntry_t;

typedef struct
{
  uint8                   key_index;
  uint8                   key_key_usage_index;
  keyUsageDescriptor_t    macKeyUsageEntry;
} macSecurityPibKeyUsageEntry_t;

typedef struct
{
  uint8                   key_index;
  uint8                   keyEntry[16];
  uint32                  frameCounter;
} macSecurityPibKeyEntry_t;

typedef struct
{
  uint8                   device_index;
  deviceDescriptor_t      macDeviceEntry;
} macSecurityPibDeviceEntry_t;

typedef struct
{
  uint8                       security_level_index;
  securityLevelDescriptor_t   macSecurityLevelEntry;
} macSecurityPibSecurityLevelEntry_t;

typedef struct
{
  uint32            timestamp;
  uint16            timestamp2;
  uint16            timeToLive;
  uint8             frameType;
  uint16            txOptions;
  uint8             txMode;
  uint8             txSched;
  uint8             retries;
  uint8             channel;
  uint8             power;
  uint8             mpduLinkQuality;
  uint8             correlation;
  int8              rssi;
  uint8             gpDuration;
  uint8             gpNumOfTx;
  uint8             gpInterframeDelay;
} macTxIntData_t;

/* For internal use only */
typedef struct
{
  uint8             frameType;
  uint8             cmdFrameId;
  uint8             flags;
} macRxIntData_t;

/* Data request parameters type */
typedef struct
{
  sAddr_t         dstAddr;      /* The address of the destination device */
  uint16          dstPanId;     /* The PAN ID of the destination device */
  uint8           srcAddrMode;  /* The source address mode */
  uint8           msduHandle;   /* Application-defined handle value associated with this data request */
  uint16          txOptions;    /* TX options bit mask */
  uint8           channel;      /* Transmit the data frame on this channel */
  uint8           power;        /* Transmit the data frame at this power level */
  uint8           gpOffset;     /* Transmit Delay for Green Power */
  uint8           gpDuration;   /* Transmit Window for Green Power */
} macDataReq_t;

/* MCPS data request type */
typedef struct
{
  macEventHdr_t   hdr;        /* Internal use only */
  sData_t         msdu;       /* Data pointer and length */
  macTxIntData_t  internal;   /* Internal use only */
  macSec_t        sec;        /* Security parameters */
  macDataReq_t    mac;        /* Data request parameters */
} macMcpsDataReq_t;

/* Data indication parameters type */
typedef struct
{
  sAddr_t   srcAddr;          /* The address of the sending device */
  sAddr_t   dstAddr;          /* The address of the destination device */
  uint32    timestamp;        /* The time, in backoffs, at which the data were received */
  uint16    timestamp2;       /* The time, in internal MAC timer units, at which the
                                 data were received */
  uint16    srcPanId;         /* The PAN ID of the sending device */
  uint16    dstPanId;         /* The PAN ID of the destination device */
  uint8     mpduLinkQuality;  /* The link quality of the received data frame */
  uint8     correlation;      /* The raw correlation value of the received data frame */
  int8      rssi;             /* The received RF power in units dBm */
  uint8     dsn;              /* The data sequence number of the received frame */
} macDataInd_t;


/* MCPS data indication type */
typedef struct
{
  macEventHdr_t  hdr;         /* Internal use only */
  sData_t        msdu;        /* Data pointer and length */
  macRxIntData_t internal;    /* Internal use only */
  macSec_t       sec;         /* Security parameters */
  macDataInd_t   mac;         /* Data indication parameters */
} macMcpsDataInd_t;

/* MCPS data confirm type */
typedef struct
{
  macEventHdr_t      hdr;              /* Contains the status of the data request operation */
  uint8              msduHandle;       /* Application-defined handle value associated with the data request */
  macMcpsDataReq_t   *pDataReq;        /* Pointer to the data request buffer for this data confirm */
  uint32             timestamp;        /* The time, in backoffs, at which the frame was transmitted */
  uint16             timestamp2;       /* The time, in internal MAC timer units, at which the
                                          frame was transmitted */
  uint8              retries;          /* The number of retries required to transmit the data frame */
  uint8              mpduLinkQuality;  /* The link quality of the received ack frame */
  uint8              correlation;      /* The raw correlation value of the received ack frame */
  int8               rssi;             /* The RF power of the received ack frame in units dBm */
} macMcpsDataCnf_t;


/* MCPS purge confirm type */
typedef struct
{
  macEventHdr_t      hdr;         /* Contains the status of the purge request operation */
  uint8              msduHandle;  /* Application-defined handle value associated with the data request */
} macMcpsPurgeCnf_t;

/* PAN descriptor type */
typedef struct
{
  sAddr_t       coordAddress;     /* The address of the coordinator sending the beacon */
  uint16        coordPanId;       /* The PAN ID of the network */
  uint16        superframeSpec;   /* The superframe specification of the network */
  uint8         logicalChannel;   /* The logical channel of the network */
  uint8         channelPage;      /* The current channel page occupied by the network */
  _Bool          gtsPermit;        /* TRUE if coordinator accepts GTS requests */
  uint8         linkQuality;      /* The link quality of the received beacon */
  uint32        timestamp;        /* The time at which the beacon was received, in backoffs */
  _Bool          securityFailure;  /* Set to TRUE if there was an error in the security processing */
  macSec_t      sec;              /* The security parameters for the received beacon frame */
} macPanDesc_t;

/* MLME associate request type */
typedef struct
{
  macSec_t    sec;                    /* The security parameters for this message */
  uint8       logicalChannel;         /* The channel on which to attempt association */
  uint8       channelPage;            /* The channel page on which to attempt association */
  sAddr_t     coordAddress;           /* Address of the coordinator with which to associate */
  uint16      coordPanId;             /* The identifier of the PAN with which to associate */
  uint8       capabilityInformation;  /* The operational capabilities of this device */
} macMlmeAssociateReq_t;

/* MLME associate response type */
typedef struct
{
  macSec_t    sec;                 /* The security parameters for this message */
  sAddrExt_t  deviceAddress;       /* The address of the device requesting association */
  uint16      assocShortAddress;   /* The short address allocated to the device */
  uint8       status;              /* The status of the association attempt */
} macMlmeAssociateRsp_t;

/* MLME disassociate request type */
typedef struct
{
  macSec_t    sec;                 /* The security parameters for this message */
  sAddr_t     deviceAddress;       /* The address of the device with which to disassociate */
  uint16      devicePanId;         /* The PAN ID of the device */
  uint8       disassociateReason;  /* The disassociate reason */
  _Bool        txIndirect;          /* Transmit Indirect */
} macMlmeDisassociateReq_t;


/* MLME orphan response type */
typedef struct
{
  macSec_t    sec;                /* The security parameters for this message */
  sAddrExt_t  orphanAddress;      /* The extended address of the device sending the orphan notification */
  uint16      shortAddress;       /* The short address of the orphaned device */
  _Bool        associatedMember;   /* Set to TRUE if the orphaned device is associated with this coordinator */
} macMlmeOrphanRsp_t;

/* MLME poll request type */
typedef struct
{
  sAddr_t     coordAddress;       /* The address of the coordinator device to poll */
  uint16      coordPanId;         /* The PAN ID of the coordinator */
  macSec_t    sec;                /* The security parameters for this message */
} macMlmePollReq_t;

/* MLME scan request type */
typedef struct
{
  uint32           scanChannels;    /* Bit mask indicating which channels to scan */
  uint8            scanType;        /* The type of scan */
  uint8            scanDuration;    /* The exponent used in the scan duration calculation */
  uint8            channelPage;     /* The channel page on which to perform the scan */
  uint8            maxResults;      /* The maximum number of PAN descriptor results */
  _Bool             permitJoining;   /* Only devices with permit joining on respond to the
                                       enahnced beacon request */
  uint8            linkQuality;     /* The device will respond to the enhanced beacon request
                                       if mpduLinkQuality is equal or higher than this value */
  uint8            percentFilter;   /* The device will then randomly determine if it is to
                                       respond to the enhanced beacon request based on meeting
                                       this probability (0 to 100%). */
  macSec_t         sec;             /* The security parameters for orphan scan */
  union {
    uint8         *pEnergyDetect;   /* Pointer to a buffer to store energy detect measurements */
    macPanDesc_t  *pPanDescriptor;  /* Pointer to a buffer to store PAN descriptors */
  } result;
} macMlmeScanReq_t;

/* MLME start request type */
typedef struct
{
  uint32      startTime;          /* The time to begin transmitting beacons relative to the received beacon */
  uint16      panId;              /* The PAN ID to use.  This parameter is ignored if panCoordinator is FALSE */
  uint8       logicalChannel;     /* The logical channel to use.  This parameter is ignored if panCoordinator is FALSE */
  uint8       channelPage;        /* The channel page to use.  This parameter is ignored if panCoordinator is FALSE */
  uint8       beaconOrder;        /* The exponent used to calculate the beacon interval */
  uint8       superframeOrder;    /* The exponent used to calculate the superframe duration */
  _Bool        panCoordinator;     /* Set to TRUE to start a network as PAN coordinator */
  _Bool        batteryLifeExt;     /* If this value is TRUE, the receiver is disabled after MAC_BATT_LIFE_EXT_PERIODS
                                     full backoff periods following the interframe spacing period of the beacon frame */
  _Bool        coordRealignment;   /* Set to TRUE to transmit a coordinator realignment prior to changing
                                     the superframe configuration */
  macSec_t    realignSec;         /* Security parameters for the coordinator realignment frame */
  macSec_t    beaconSec;          /* Security parameters for the beacon frame */
} macMlmeStartReq_t;

/* MAC_MlmeSyncReq type */
typedef struct
{
  uint8       logicalChannel;     /* The logical channel to use */
  uint8       channelPage;        /* The channel page to use */
  uint8       trackBeacon;        /* Set to TRUE to continue tracking beacons after synchronizing with the
                                     first beacon.  Set to FALSE to only synchronize with the first beacon */
} macMlmeSyncReq_t;

/* MAC_MLME_ASSOCIATE_IND type */
typedef struct
{
  macEventHdr_t   hdr;                    /* The event header */
  sAddrExt_t      deviceAddress;          /* The address of the device requesting association */
  uint8           capabilityInformation;  /* The operational capabilities of the device requesting association */
  macSec_t        sec;                    /* The security parameters for this message */
} macMlmeAssociateInd_t;

/* MAC_MLME_ASSOCIATE_CNF type */
typedef struct
{
  macEventHdr_t   hdr;                    /* Event header contains the status of the associate attempt */
  uint16          assocShortAddress;      /* If successful, the short address allocated to this device */
  macSec_t        sec;                    /* The security parameters for this message */
} macMlmeAssociateCnf_t;

/* MAC_MLME_DISASSOCIATE_IND type */
typedef struct
{
  macEventHdr_t   hdr;                    /* The event header */
  sAddrExt_t      deviceAddress;          /* The address of the device sending the disassociate command */
  uint8           disassociateReason;     /* The disassociate reason */
  macSec_t        sec;                    /* The security parameters for this message */
} macMlmeDisassociateInd_t;

/* MAC_MLME_DISASSOCIATE_CNF type */
typedef struct
{
  macEventHdr_t   hdr;                    /* Event header contains the status of the disassociate attempt */
  sAddr_t         deviceAddress;          /* The address of the device that has either requested disassociation
                                             or been instructed to disassociate by its coordinator */
  uint16          panId;                  /* The pan ID of the device that has either requested disassociation
                                             or been instructed to disassociate by its coordinator */
} macMlmeDisassociateCnf_t;

/* MAC_MLME_BEACON_NOTIFY_IND type */
typedef struct
{
  macEventHdr_t  hdr;             /* The event header */
  uint8          bsn;             /* The beacon sequence number */
  macPanDesc_t   *pPanDesc;       /* The PAN descriptor for the received beacon */
  uint8          pendAddrSpec;    /* The beacon pending address specification */
  uint8          *pAddrList;      /* The list of device addresses for which the sender of the beacon has data */
  uint8          sduLength;       /* The number of bytes in the beacon payload of the beacon frame */
  uint8          *pSdu;           /* The beacon payload */
} macMlmeBeaconNotifyInd_t;

/* MAC_MLME_ORPHAN_IND type */
typedef struct
{
  macEventHdr_t   hdr;            /* The event header */
  sAddrExt_t      orphanAddress;  /* The address of the orphaned device */
  macSec_t        sec;            /* The security parameters for this message */
} macMlmeOrphanInd_t;

/* MAC_MLME_SCAN_CNF type */
typedef struct
{
  macEventHdr_t   hdr;                /* Event header contains the status of the scan request */
  uint8           scanType;           /* The type of scan requested */
  uint8           channelPage;        /* The channel page of the scan */
  uint32          unscannedChannels;  /* Bit mask of channels that were not scanned */
  uint8           resultListSize;     /* The number of PAN descriptors returned in the results list */
  union
  {
    uint8         *pEnergyDetect;     /* The list of energy measurements, one for each channel scanned */
    macPanDesc_t  *pPanDescriptor;    /* The list of PAN descriptors, one for each beacon found */
  } result;
} macMlmeScanCnf_t;

/* MAC_MLME_START_CNF type */
typedef struct
{
  macEventHdr_t   hdr;            /* Event header contains the status of the start request */
} macMlmeStartCnf_t;

/* MAC_MLME_SYNC_LOSS_IND type */
typedef struct
{
  macEventHdr_t   hdr;            /* Event header contains the reason that synchronization was lost */
  uint16          panId;          /* The PAN ID of the realignment */
  uint8           logicalChannel; /* The logical channel of the realignment */
  uint8           channelPage;    /* The channel page of the realignment */
  macSec_t        sec;            /* The security parameters for this message */
} macMlmeSyncLossInd_t;

/* MAC_MLME_POLL_CNF type */
typedef struct
{
  macEventHdr_t   hdr;            /* Event header contains the status of the poll request */
  uint8           framePending;   /* Set if framePending bit in data packet is set */
} macMlmePollCnf_t;

/* MAC_MLME_COMM_STATUS_IND type */
typedef struct
{
  macEventHdr_t   hdr;            /* Event header contains the status for this event */
  sAddr_t         srcAddr;        /* The source address associated with the event */
  sAddr_t         dstAddr;        /* The destination address associated with the event */
  uint16          panId;          /* The PAN ID associated with the event */
  uint8           reason;         /* The reason the event was generated */
  macSec_t        sec;            /* The security parameters for this message */
} macMlmeCommStatusInd_t;

/* MAC_MLME_POLL_IND type */
typedef struct
{
  macEventHdr_t   hdr;
  sAddr_t         srcAddr;   /* Short address of the device sending the data request */
  uint16          srcPanId;       /* Pan ID of the device sending the data request */
  uint8           noRsp;          /* indication that no MAC_McpsDataReq() is required.
                                   * It is set when MAC_MLME_POLL_IND is generated,
                                   * to simply indicate that a received data request frame
                                   * was acked with pending bit cleared. */
} macMlmePollInd_t;

/* Union of callback structures */
typedef union
{
  macEventHdr_t            hdr;
  macMlmeAssociateInd_t    associateInd;      /* MAC_MLME_ASSOCIATE_IND */
  macMlmeAssociateCnf_t    associateCnf;      /* MAC_MLME_ASSOCIATE_CNF */
  macMlmeDisassociateInd_t disassociateInd;   /* MAC_MLME_DISASSOCIATE_IND */
  macMlmeDisassociateCnf_t disassociateCnf;   /* MAC_MLME_DISASSOCIATE_CNF */
  macMlmeBeaconNotifyInd_t beaconNotifyInd;   /* MAC_MLME_BEACON_NOTIFY_IND */
  macMlmeOrphanInd_t       orphanInd;         /* MAC_MLME_ORPHAN_IND */
  macMlmeScanCnf_t         scanCnf;           /* MAC_MLME_SCAN_CNF */
  macMlmeStartCnf_t        startCnf;          /* MAC_MLME_START_CNF */
  macMlmeSyncLossInd_t     syncLossInd;       /* MAC_MLME_SYNC_LOSS_IND */
  macMlmePollCnf_t         pollCnf;           /* MAC_MLME_POLL_CNF */
  macMlmeCommStatusInd_t   commStatusInd;     /* MAC_MLME_COMM_STATUS_IND */
  macMlmePollInd_t         pollInd;           /* MAC_MLME_POLL_IND */
  macMcpsDataCnf_t         dataCnf;           /* MAC_MCPS_DATA_CNF */
  macMcpsDataInd_t         dataInd;           /* MAC_MCPS_DATA_IND */
  macMcpsPurgeCnf_t        purgeCnf;          /* MAC_MCPS_PURGE_CNF */
} macCbackEvent_t;

/* Configurable parameters */
typedef struct
{
  uint8   txDataMax;                /* maximum number of data frames in transmit queue */
  uint8   txMax;                    /* maximum number of frames of all types in transmit queue */
  uint8   rxMax;                    /* maximum number of command and data frames in receive queue */
  uint8   dataIndOffset;            /* allocate additional bytes in the data indication for
                                       application-defined headers */
  uint8   maxDeviceTableEntries;    /* max Device Table entries */
  _Bool    appPendingQueue;          /* determine whether MAC_MLME_POLL_IND will be sent to the application or not
                                       when data request is received and no pending frame is found in the MAC */
  uint8   macMaxFrameSize;          /* Maximum application data length without security */
} macCfg_t;


/* ------------------------------------------------------------------------------------------------
 *                                        Internal Functions
 * ------------------------------------------------------------------------------------------------
 */

/* These functions are used when creating the OSAL MAC task.  They must not be used for any
 * other purpose.
 */
extern void macTaskInit(uint8 taskId);
extern uint16 macEventLoop(uint8 taskId, uint16 events);


/* ------------------------------------------------------------------------------------------------
 *                                           Functions
 * ------------------------------------------------------------------------------------------------
 */

/**************************************************************************************************
 * @fn          MAC_Init
 *
 * @brief       This function initializes the MAC subsystem.  It must be called once when the
 *              software system is started and before any other function in the MAC API
 *              is called.
 *
 * input parameters
 *
 * None.
 *
 * output parameters
 *
 * None.
 *
 * @return      None.
 **************************************************************************************************
 */
extern void MAC_Init(void);

/**************************************************************************************************
 * @fn          MAC_InitDevice
 *
 * @brief       This function initializes the MAC to associate with a non
 *              beacon-enabled network.  This function would be used to
 *              initialize a device as an RFD.  If this function is used it
 *              must be called during application initialization before any
 *              other function in the data or management API is called.
 *
 * input parameters
 *
 * None.
 *
 * output parameters
 *
 * None.
 *
 * @return      None.
 **************************************************************************************************
 */
extern void MAC_InitDevice(void);

/**************************************************************************************************
 * @fn          MAC_InitCoord
 *
 * @brief       This function initializes the MAC for operation as a
 *              coordinator.  A coordinator can start a network, accept
 *              associate requests from other devices, send beacons, send
 *              indirect data, and other operations.  This function would
 *              be used to initialize a device as an FFD.  If this function
 *              is used it must be called during application initialization
 *              before any other function in the data or management API
 *              is called.
 *
 * input parameters
 *
 * None.
 *
 * output parameters
 *
 * None.
 *
 * @return      None.
 **************************************************************************************************
 */
extern void MAC_InitCoord(void);

/**************************************************************************************************
 * @fn          MAC_InitBeaconCoord
 *
 * @brief       This function initializes the MAC for operation as a coordinator in a
 *              beacon-enabled network.  If this function is used it must
 *              be called during application initialization before any other
 *              function in the data or management API is called.
 *
 * input parameters
 *
 * None.
 *
 * output parameters
 *
 * None.
 *
 * @return      None.
 **************************************************************************************************
 */
extern void MAC_InitBeaconCoord(void);

/**************************************************************************************************
 * @fn          MAC_InitBeaconTrack
 *
 * @brief       This function initializes the MAC to allow it to associate
 *              with and track a beacon-enabled network.  If this function is
 *              used it must be called during application initialization
 *              before any other function in the data or management API
 *              is called.
 *
 * input parameters
 *
 * None.
 *
 * output parameters
 *
 * None.
 *
 * @return      None.
 **************************************************************************************************
 */
extern void MAC_InitBeaconDevice(void);

/**************************************************************************************************
 * @fn          MAC_McpsDataReq
 *
 * @brief       This function sends application data to the MAC for
 *              transmission in a MAC data frame.
 *
 * input parameters
 *
 * @param       pData - Pointer to parameters structure.
 *
 * output parameters
 *
 * None.
 *
 * @return      None.
 **************************************************************************************************
 */
extern void MAC_McpsDataReq(macMcpsDataReq_t *pData);

/**************************************************************************************************
 * @fn          MAC_McpsPurgeReq
 *
 * @brief       This function purges and discards a data request from the
 *              MAC data queue.  When the operation is complete the MAC sends
 *              a MAC_MCPS_PURGE_CNF.
 *
 * input parameters
 *
 * @param       msduHandle - The application-defined handle value
 *
 * output parameters
 *
 * None.
 *
 * @return      None.
 **************************************************************************************************
 */
extern void MAC_McpsPurgeReq(uint8 msduHandle);

/**************************************************************************************************
 * @fn          MAC_McpsDataAlloc
 *
 * @brief       This direct-execute function simplifies the allocation and
 *              preparation of the data buffer MAC_McpsDataReq().  The
 *              function allocates a buffer and prepares the data pointer.
 *
 * input parameters
 *
 * @param       len - Length of application data in bytes.
 * @param       securityLevel - Security level used for this frame.
 * @param       keyIdMode - Key ID mode used for this frame.
 *
 * output parameters
 *
 * None.
 *
 * @return      Returns a pointer to the allocated buffer.  If the function
 *              fails for any reason it returns NULL.
 **************************************************************************************************
 */
extern macMcpsDataReq_t *MAC_McpsDataAlloc(uint8 len, uint8 securityLevel, uint8 keyIdMode);

/**************************************************************************************************
 * @fn          MAC_MlmeAssociateReq
 *
 * @brief       This function sends an associate request to a coordinator
 *              device.  The application shall attempt to associate only with
 *              a PAN that is currently allowing association, as indicated
 *              in the results of the scanning procedure. In a beacon-enabled
 *              PAN the beacon order and superframe order must be set by using
 *              MAC_MlmeSetReq() before making the call to MAC_MlmeAssociateReq().
 *              If not, the associate request frame is likely to be transmitted
 *              outside the superframe.  When the associate request is complete
 *              the MAC sends a MAC_MLME_ASSOCIATE_CNF to the application.
 *
 * input parameters
 *
 * @param       pData - Pointer to parameters structure.
 *
 * output parameters
 *
 * None.
 *
 * @return      None.
 **************************************************************************************************
 */
extern void MAC_MlmeAssociateReq(macMlmeAssociateReq_t *pData);

/**************************************************************************************************
 * @fn          MAC_MlmeAssociateRsp
 *
 * @brief       This function sends an associate response to a device
 *              requesting to associate.  This function must be called after
 *              receiving a MAC_MLME_ASSOCIATE_IND.  When the associate response is
 *              complete the MAC sends a MAC_MLME_COMM_STATUS_IND to the application
 *              to indicate the success or failure of the operation.
 *
 * input parameters
 *
 * @param       pData - Pointer to parameters structure.
 *
 * output parameters
 *
 * None.
 *
 * @return      MAC_SUCCESS or MAC error code.
 **************************************************************************************************
 */
extern uint8 MAC_MlmeAssociateRsp(macMlmeAssociateRsp_t *pData);

/**************************************************************************************************
 * @fn          MAC_MlmeDisassociateReq
 *
 * @brief       This function is used by an associated device to notify the
 *              coordinator of its intent to leave the PAN.  It is also used
 *              by the coordinator to instruct an associated device to leave
 *              the PAN.  When the disassociate is complete the MAC sends a
 *              MAC_MLME_DISASSOCIATE_CNF to the application.
 *
 * input parameters
 *
 * @param       pData - Pointer to parameters structure.
 *
 * output parameters
 *
 * None.
 *
 * @return      None.
 **************************************************************************************************
 */
extern void MAC_MlmeDisassociateReq(macMlmeDisassociateReq_t *pData);

/**************************************************************************************************
 * @fn          MAC_MlmeGetReq
 *
 * @brief       This direct execute function retrieves an attribute value
 *              from the MAC PIB.
 *
 * input parameters
 *
 * @param       pibAttribute - The attribute identifier.
 * @param       pValue - pointer to the attribute value.
 *
 * output parameters
 *
 * @param       pValue - pointer to the attribute value.
 *
 * @return      The status of the request, as follows:
 *              MAC_SUCCESS Operation successful.
 *              MAC_UNSUPPORTED_ATTRIBUTE Attribute not found.
 *
 **************************************************************************************************
 */
extern uint8 MAC_MlmeGetReq(uint8 pibAttribute, void *pValue);

/**************************************************************************************************
 * @fn          MAC_MlmeGetSecurityReq
 *
 * @brief       This direct execute function retrieves an attribute value
 *              from the MAC Secutity PIB. This function only exists when
 *              FEATURE_MAC_SECURITY is defined.
 *
 * input parameters
 *
 * @param       pibAttribute - The attribute identifier.
 * @param       pValue - pointer to the attribute value.
 *
 * output parameters
 *
 * @param       pValue - pointer to the attribute value.
 *
 * @return      The status of the request, as follows:
 *              MAC_SUCCESS Operation successful.
 *              MAC_UNSUPPORTED_ATTRIBUTE Attribute not found.
 *
 **************************************************************************************************
 */
extern uint8 MAC_MlmeGetSecurityReq(uint8 pibAttribute, void *pValue);

/**************************************************************************************************
 * @fn          MAC_MlmeOrphanRsp
 *
 * @brief       This function is called in response to an orphan notification
 *              from a peer device.  This function must be called after
 *              receiving a MAC_MLME_ORPHAN_IND.  When the orphan response is
 *              complete the MAC sends a MAC_MLME_COMM_STATUS_IND to the
 *              application to indicate the success or failure of the operation.
 *
 * input parameters
 *
 * @param       pData - Pointer to parameters structure.
 *
 * output parameters
 *
 * None.
 *
 * @return      None.
 **************************************************************************************************
 */
extern void MAC_MlmeOrphanRsp(macMlmeOrphanRsp_t *pData);

/**************************************************************************************************
 * @fn          MAC_MlmePollReq
 *
 * @brief       This function is used to request pending data from the
 *              coordinator.  When the poll request is complete the MAC sends
 *              a MAC_MLME_POLL_CNF to the application.  If a data frame of
 *              nonzero length is received from the coordinator the MAC sends
 *              a MAC_MLME_POLL_CNF with status MAC_SUCCESS and then sends a
 *              MAC_MCPS_DATA_IND with the data.
 *
 * input parameters
 *
 * @param       pData - Pointer to parameters structure.
 *
 * output parameters
 *
 * None.
 *
 * @return      None.
 **************************************************************************************************
 */
extern void MAC_MlmePollReq(macMlmePollReq_t *pData);

/**************************************************************************************************
 * @fn          MAC_MlmeResetReq
 *
 * @brief       This direct execute function resets the MAC.  This function
 *              must be called once at system startup before any other
 *              function in the management API is called.
 *
 * input parameters
 *
 * @param       setDefaultPib - Set to TRUE to reset the MAC PIB to its
 *                              default values.
 *
 * output parameters
 *
 * None.
 *
 * @return      Returns MAC_SUCCESS always.
 *
 **************************************************************************************************
 */
extern uint8 MAC_MlmeResetReq(_Bool setDefaultPib);

/**************************************************************************************************
 * @fn          MAC_MlmeScanReq
 *
 * @brief       This function initiates an energy detect, active, passive,
 *              or orphan scan on one or more channels.  An energy detect
 *              scan measures the peak energy on each requested channel.
 *              An active scan sends a beacon request on each channel and
 *              then listening for beacons.  A passive scan is a receive-only
 *              operation that listens for beacons on each channel.  An orphan
 *              scan is used to locate the coordinator with which the scanning
 *              device had previously associated.  When a scan operation is
 *              complete the MAC sends a MAC_MLME_SCAN_CNF to the application.
 *
 * input parameters
 *
 * @param       pData - Pointer to parameters structure.
 *
 * output parameters
 *
 * None.
 *
 * @return      None.
 **************************************************************************************************
 */
extern void MAC_MlmeScanReq(macMlmeScanReq_t *pData);

/**************************************************************************************************
 * @fn          MAC_MlmeSetReq
 *
 * @brief       This direct execute function sets an attribute value
 *              in the MAC PIB.
 *
 * input parameters
 *
 * @param       pibAttribute - The attribute identifier.
 * @param       pValue - pointer to the attribute value.
 *
 * output parameters
 *
 * None.
 *
 * @return      The status of the request, as follows:
 *              MAC_SUCCESS Operation successful.
 *              MAC_UNSUPPORTED_ATTRIBUTE Attribute not found.
 *
 **************************************************************************************************
 */
extern uint8 MAC_MlmeSetReq(uint8 pibAttribute, void *pValue);

/**************************************************************************************************
 * @fn          MAC_MlmeSetSecurityReq
 *
 * @brief       This direct execute function sets an attribute value
 *              in the MAC Security PIB. This function only exists when
 *              FEATURE_MAC_SECURITY is defined.
 *
 * input parameters
 *
 * @param       pibAttribute - The attribute identifier.
 * @param       pValue - pointer to the attribute value.
 *
 * output parameters
 *
 * None.
 *
 * @return      The status of the request, as follows:
 *              MAC_SUCCESS Operation successful.
 *              MAC_UNSUPPORTED_ATTRIBUTE Attribute not found.
 *
 **************************************************************************************************
 */
extern uint8 MAC_MlmeSetSecurityReq(uint8 pibAttribute, void *pValue);

/**************************************************************************************************
 * @fn          MAC_MlmeStartReq
 *
 * @brief       This function is called by a coordinator or PAN coordinator
 *              to start or reconfigure a network.  Before starting a
 *              network the device must have set its short address.  A PAN
 *              coordinator sets the short address by setting the attribute
 *              MAC_SHORT_ADDRESS.  A coordinator sets the short address
 *              through association.  When the operation is complete the
 *              MAC sends a MAC_MLME_START_CNF to the application.
 *
 * input parameters
 *
 * @param       pData - Pointer to parameters structure.
 *
 * output parameters
 *
 * None.
 *
 * @return      None.
 **************************************************************************************************
 */
extern void MAC_MlmeStartReq(macMlmeStartReq_t *pData);

/**************************************************************************************************
 * @fn          MAC_MlmeSyncReq
 *
 * @brief       This function requests the MAC to synchronize with the
 *              coordinator by acquiring and optionally tracking its beacons.
 *              Synchronizing with the coordinator is recommended before
 *              associating in a beacon-enabled network.  If the beacon could
 *              not be located on its initial search or during tracking, the
 *              MAC sends a MAC_MLME_SYNC_LOSS_IND to the application with
 *              status MAC_BEACON_LOSS.
 *
 * input parameters
 *
 * @param       pData - Pointer to parameters structure.
 *
 * output parameters
 *
 * None.
 *
 * @return      None.
 **************************************************************************************************
 */
extern void MAC_MlmeSyncReq(macMlmeSyncReq_t *pData);

/**************************************************************************************************
 * @fn          MAC_PwrOffReq
 *
 * @brief       This direct execute function requests the MAC to power off
 *              the radio hardware and go to sleep.  If the MAC is able to
 *              power off it will execute its power off procedure and return
 *              MAC_SUCCESS.  If the MAC is unable to sleep it will return
 *              MAC_DENIED.  The MAC is unable to sleep when it is executing
 *              certain procedures, such as a scan, data request, or association.
 *              If this function is called when the MAC is already in sleep mode
 *              it will return MAC_SUCCESS but do nothing.
 *
 * input parameters
 *
 * @param       mode - The desired low power mode.
 *
 * output parameters
 *
 * None.
 *
 * @return      The status of the request, as follows:
 *              MAC_SUCCESS  Operation successful; the MAC is powered off.
 *              MAC_DENIED  The MAC was not able to power off.
 **************************************************************************************************
 */
extern uint8 MAC_PwrOffReq(uint8 mode);

/**************************************************************************************************
 * @fn          MAC_PwrOnReq
 *
 * @brief       This function requests the MAC to power on the radio hardware
 *              and wake up.  When the power on procedure is complete the MAC
 *              will send a MAC_PWR_ON_CNF to the application.
 *
 * input parameters
 *
 * None.
 *
 * output parameters
 *
 * None.
 *
 * @return      None.
 **************************************************************************************************
 */
extern void MAC_PwrOnReq(void);

/**************************************************************************************************
 * @fn          MAC_PwrMode
 *
 * @brief       This function returns the current power mode of the MAC.
 *
 * input parameters
 *
 * None.
 *
 * output parameters
 *
 * None.
 *
 * @return      The current power mode of the MAC.
 **************************************************************************************************
 */
extern uint8 MAC_PwrMode(void);

/**************************************************************************************************
 * @fn          MAC_PwrNextTimeout
 *
 * @brief       This function returns the next MAC timer expiration in 320 usec units.  If no
 *              timer is running it returns zero.
 *
 * input parameters
 *
 * None.
 *
 * output parameters
 *
 * None.
 *
 * @return      The next MAC timer expiration or zero.
 **************************************************************************************************
*/
extern uint32 MAC_PwrNextTimeout(void);

/**************************************************************************************************
 * @fn          MAC_RandomByte
 *
 * @brief       This function returns a random byte from the MAC random number generator.
 *
 * input parameters
 *
 * None.
 *
 * output parameters
 *
 * None.
 *
 * @return      A random byte.
 **************************************************************************************************
 */
extern uint8 MAC_RandomByte(void);

/**************************************************************************************************
 * @fn          MAC_ResumeReq
 *
 * @brief       This direct execute function resumes the MAC after a successful return from
 *              MAC_YieldReq().
 *
 * input parameters
 *
 * None.
 *
 * output parameters
 *
 * None.
 *
 * @return      None.
 **************************************************************************************************
 */
extern void MAC_ResumeReq(void);

/**************************************************************************************************
 * @fn          MAC_MlmeSetActivePib
 *
 * @brief       This direct execute function sets the active MAC PIB.
 *
 * input parameters
 *
 * @param       pPib - pointer to the PIB structure.
 *
 * output parameters
 *
 * @return      None.
 *
 **************************************************************************************************
 */
void MAC_MlmeSetActivePib( void* pPib );

/**************************************************************************************************
 * @fn          MAC_MlmeSetActivePib
 *
 * @brief       This direct execute function sets the active MAC security PIB.
 *
 * input parameters
 *
 * @param       pSecPib - pointer to the security PIB structure.
 *
 * output parameters
 *
 * @return      None.
 *
 **************************************************************************************************
 */
void MAC_MlmeSetActiveSecurityPib( void* pSecPib );

/**************************************************************************************************
 * @fn          MAC_SrcMatchEnable
 *
 * @brief      Enabled AUTOPEND and source address matching. This function shall not
 *             be called from ISR. It is not thread safe.
 *
 * @return     None
 **************************************************************************************************
 */
extern void MAC_SrcMatchEnable ( void );

/**************************************************************************************************
 * @fn          MAC_SrcMatchAddEntry
 *
 * @brief       Add a short or extended address to source address table. This
 *              function shall not be called from ISR. It is not thread safe.
 *
 * @param       addr - a pointer to sAddr_t which contains addrMode
 *                     and a union of a short 16-bit MAC address or an extended
 *                     64-bit MAC address to be added to the source address table.
 * @param       panID - the device PAN ID. It is only used when the addr is
 *                      using short address
 *
 * @return      MAC_SUCCESS or MAC_NO_RESOURCES (source address
 *              table full) or MAC_DUPLICATED_ENTRY (the entry added is duplicated),
 *              or MAC_INVALID_PARAMETER if the input parameters are invalid.
 **************************************************************************************************
 */
extern uint8 MAC_SrcMatchAddEntry ( sAddr_t *addr, uint16 panID );

/**************************************************************************************************
 * @fn         MAC_SrcMatchDeleteEntry
 *
 * @brief      Delete a short or extended address from source address table.
 *             This function shall not be called from ISR. It is not thread safe.
 *
 * @param      addr - a pointer to sAddr_t which contains addrMode
 *                    and a union of a short 16-bit MAC address or an extended
 *                    64-bit MAC address to be deleted from the source address table.
 * @param      panID - the device PAN ID. It is only used when the addr is
 *                     using short address
 *
 * @return     MAC_SUCCESS or MAC_INVALID_PARAMETER (address to be deleted
 *                  cannot be found in the source address table).
 **************************************************************************************************
 */
extern uint8 MAC_SrcMatchDeleteEntry ( sAddr_t *addr, uint16 panID  );

/**************************************************************************************************
 * @fn          MAC_SrcMatchAckAllPending
 *
 * @brief       Enabled/disable acknowledging all packets with pending bit set
 *              The application normally enables it when adding new entries to
 *              the source address table fails due to the table is full, or
 *              disables it when more entries are deleted and the table has
 *              empty slots.
 *
 * @param       option - TRUE (acknowledging all packets with pending field set)
 *                       FALSE (acknowledging all packets with pending field cleared)
 *
 * @return      none
 **************************************************************************************************
 */
extern void MAC_SrcMatchAckAllPending ( uint8 option  );

/**************************************************************************************************
 * @fn          MAC_SrcMatchCheckAllPending
 *
 * @brief       Check if acknowledging all packets with pending bit set
 *              is enabled.
 *
 * @param       none
 *
 * @return      MAC_AUTOACK_PENDING_ALL_ON or MAC_AUTOACK_PENDING_ALL_OFF
 **************************************************************************************************
 */
extern uint8 MAC_SrcMatchCheckAllPending ( void );

/**************************************************************************************************
 * @fn          MAC_SelectRadioRegTable
 *
 * @brief       Select radio register table in case multiple register tables are included
 *              in the build
 *
 * @param       txPwrTblIdx - TX power register value table index
 * @param       rssiAdjIdx - RSSI adjustment value index
 *
 * @return      none
 **************************************************************************************************
 */
extern void MAC_SetRadioRegTable ( uint8 txPwrTblIdx, uint8 rssiAdjIdx );

/**************************************************************************************************
 * @fn          MAC_CbackEvent
 *
 * @brief       This callback function sends MAC events to the application.
 *              The application must implement this function.  A typical
 *              implementation of this function would allocate an OSAL message,
 *              copy the event parameters to the message, and send the message
 *              to the application's OSAL event handler.  This function may be
 *              executed from task or interrupt context and therefore must
 *              be reentrant.
 *
 * input parameters
 *
 * @param       pData - Pointer to parameters structure.
 *
 * output parameters
 *
 * None.
 *
 * @return      None.
 **************************************************************************************************
 */
extern void MAC_CbackEvent(macCbackEvent_t *pData);

/**************************************************************************************************
 * @fn          MAC_CbackCheckPending
 *
 * @brief       This callback function returns the number of pending indirect messages queued in
 *              the application. Most applications do not queue indirect data and can simply
 *              always return zero. The number of pending indirect messages only needs to be
 *              returned if macCfg.appPendingQueue to TRUE.
 *
 * input parameters
 *
 * None.
 *
 * output parameters
 *
 * None.
 *
 * @return      The number of indirect messages queued in the application or zero.
 **************************************************************************************************
*/
extern uint8 MAC_CbackCheckPending(void);

/**************************************************************************************************
 * @fn          MAC_CbackQueryRetransmit
 *
 * @brief       This function callback function returns whether or not to continue MAC
 *              retransmission.
 *              A return value '0x00' will indicate no continuation of retry and a return value
 *              '0x01' will indicate to continue retransmission. This callback function shall be
 *              used to stop continuing retransmission for RF4CE.
 *              MAC shall call this callback function whenever it finishes transmitting a packet
 *              for macMaxFrameRetries times.
 *
 * input parameters
 *
 * None.
 *
 * output parameters
 *
 * None.
 *
 * @return      0x00 to stop retransmission, 0x01 to continue retransmission.
 **************************************************************************************************
*/
extern uint8 MAC_CbackQueryRetransmit(void);

/**************************************************************************************************
 * @fn          MAC_YieldReq
 *
 * @brief       Checks if the mac is in idle or polling state by calling macStateIdleOrPolling().
 *
 * input parameters
 *
 * None.
 *
 * output parameters
 *
 * None.
 *
 * @return      The status of the request, as follows:
 *              MAC_SUCCESS  The MAC is ready to yield.
 *              MAC_DENIED  The MAC cannot yield now.
 **************************************************************************************************
 */
extern uint8 MAC_YieldReq(void);

/**************************************************************************************************
 * @fn          macUpdatePanId
 *
 * @brief       Update Device Table entry and PIB with new Pan Id
 *
 *
 * input parameters
 *
 * @param       panId - the new Pan ID
 *
 * output parameters
 *
 * @return      None
 **************************************************************************************************/
extern void macUpdatePanId(uint16 panId);

/**************************************************************************************************
*/





#line 53 "F:\\Workspace\\zstack_iar_zf\\Components\\zmac\\f8w\\zmac_internal.h"

/********************************************************************************************************
 *                                                DEFINES
 ********************************************************************************************************/

// MAC Type Indication


// PHY transiver output power values
#line 70 "F:\\Workspace\\zstack_iar_zf\\Components\\zmac\\f8w\\zmac_internal.h"

// MAC PIB Attributes
enum
{
  ZMacAckWaitDuration                   = 0x40,
  ZMacAssociationPermit                 = 0x41,
  ZMacAutoRequest                       = 0x42,
  ZMacBattLifeExt                       = 0x43,
  ZMacBattLeftExtPeriods                = 0x44,

  ZMacBeaconMSDU                        = 0x45,
  ZMacBeaconMSDULength                  = 0x46,
  ZMacBeaconOrder                       = 0x47,
  ZMacBeaconTxTime                      = 0x48,
  ZMacBSN                               = 0x49,

  ZMacCoordExtendedAddress              = 0x4A,
  ZMacCoordShortAddress                 = 0x4B,
  ZMacDSN                               = 0x4C,
  ZMacGTSPermit                         = 0x4D,
  ZMacMaxCSMABackoffs                   = 0x4E,

  ZMacMinBE                             = 0x4F,
  ZMacPanId                             = 0x50,
  ZMacPromiscuousMode                   = 0x51,
  ZMacRxOnIdle                          = 0x52,
  ZMacShortAddress                      = 0x53,

  ZMacSuperframeOrder                   = 0x54,
  ZMacTransactionPersistenceTime        = 0x55,
  ZMacAssociatedPanCoord                = 0x56,
  ZMacMaxBE                             = 0x57,
  ZMacMaxFrameTotalWaitTime             = 0x58,

  ZMacMaxFrameRetries                   = 0x59,
  ZMacResponseWaitTime                  = 0x5A,
  ZMacSyncSymbolOffset                  = 0x5B,
  ZMacTimestampSupported                = 0x5C,
  ZMacSecurityEnabled                   = 0x5D,

  // Proprietary Items
  ZMacPhyTransmitPowerSigned            = 0xE0,
  ZMacChannel                           = 0xE1,
  ZMacExtAddr                           = 0xE2,
  ZMacAltBE                             = 0xE3,
  ZMacDeviceBeaconOrder                 = 0xE4,
  ZMacRf4cePowerSavings                 = 0xE5,
  ZMacFrameVersionSupport               = 0xE6,
    
  // Diagnostics Items
  ZMacDiagsRxCrcPass                    = 0xE7,
  ZMacDiagsRxCrcFail                    = 0xE8,
  ZMacDiagsRxBcast                      = 0xE9,
  ZMacDiagsTxBcast                      = 0xEA,
  ZMacDiagsRxUcast                      = 0xEB,
  ZMacDiagsTxUcast                      = 0xEC,
  ZMacDiagsTxUcastRetry                 = 0xED,
  ZMacDiagsTxUcastFail                  = 0xEE,

#line 154 "F:\\Workspace\\zstack_iar_zf\\Components\\zmac\\f8w\\zmac_internal.h"

  // Junk
  ZMacACLDefaultSecurityMaterialLength  = 0,     // not implemented
  ZMacTxGTSId                           = 1,     // not implemented
  ZMacUpperLayerType                    = 2,     // not implemented
  ZMacRxGTSId                           = 3,     // not implemented
  ZMacSnoozePermit                      = 4      // not implemented
};

typedef uint8 ZMacAttributes_t;

// Status type
typedef uint8 ZMacStatus_t;

/* Definition of scan type */





/* Adding Enhanced Active Scan request/ Enhanced beacon request */ 

// Association Status Field Values




// Disassociation Reason Codes







// TX Option flags
#line 197 "F:\\Workspace\\zstack_iar_zf\\Components\\zmac\\f8w\\zmac_internal.h"





// LQI to Cost mapping
#line 210 "F:\\Workspace\\zstack_iar_zf\\Components\\zmac\\f8w\\zmac_internal.h"

/* Number of bytes to allocate for ED scan; matches ED_SCAN_MAXCHANNELS in nwk.h */


#line 222 "F:\\Workspace\\zstack_iar_zf\\Components\\zmac\\f8w\\zmac_internal.h"



/********************************************************************************************************
 *                                            TYPE DEFINITIONS
 ********************************************************************************************************/





#line 54 "F:\\Workspace\\zstack_iar_zf\\Components\\zmac\\ZMAC.h"

/*********************************************************************
 * MACROS
 */

/* Maximum length of the beacon payload */




/*********************************************************************
 * CONSTANTS
 */

#line 91 "F:\\Workspace\\zstack_iar_zf\\Components\\zmac\\ZMAC.h"

/* LQI adjustment parameters */
#line 99 "F:\\Workspace\\zstack_iar_zf\\Components\\zmac\\ZMAC.h"

/*********************************************************************
 * TYPEDEFS
 */

/* ZMAC event header type */
typedef struct
{
  uint8   Event;              /* ZMAC event */
  uint8   Status;             /* ZMAC status */
} ZMacEventHdr_t;

/* Common security type */
typedef struct
{
  uint8 KeySource[8];
  uint8 SecurityLevel;
  uint8 KeyIdMode;
  uint8 KeyIndex;
}ZMacSec_t;

/* PAN descriptor type */
typedef struct
{
  zAddrType_t   CoordAddress;
  uint16        CoordPANId;
  uint16        SuperframeSpec;
  uint8         LogicalChannel;
  uint8         ChannelPage;
  uint8         GTSPermit;
  uint8         LinkQuality;
  uint32        TimeStamp;
  uint8         SecurityFailure;
  ZMacSec_t     Sec;
} ZMacPanDesc_t;

/* Communication status indication type */
typedef struct
{
  ZMacEventHdr_t hdr;
  zAddrType_t    SrcAddress;
  zAddrType_t    DstAddress;
  uint16         PANId;
  uint8          Reason;
  ZMacSec_t      Sec;
} ZMacCommStatusInd_t;

/* SYNC */

typedef struct
{
  uint8 LogicalChannel;     /* The logical channel to use */
  uint8 ChannelPage;        /* The channel page to use */
  uint8 TrackBeacon;        /* Set to TRUE to continue tracking beacons after synchronizing with the
                               first beacon.  Set to FALSE to only synchronize with the first beacon */
}ZMacSyncReq_t;

/* DATA TYPES */

/* Data request parameters type */
typedef struct
{
  zAddrType_t   DstAddr;
  uint16        DstPANId;
  uint8         SrcAddrMode;
  uint8         Handle;
  uint16        TxOptions;
  uint8         Channel;
  uint8         Power;
  uint8         GpOffset;
  uint8         GpDuration;
  ZMacSec_t     Sec;
  uint8         msduLength;
  uint8        *msdu;
} ZMacDataReq_t;

/* Data confirm type */
typedef struct
{
  ZMacEventHdr_t hdr;
  uint8          msduHandle;
  ZMacDataReq_t  *pDataReq;
  uint32         Timestamp;
  uint16         Timestamp2;
  uint8          retries;
  uint8          mpduLinkQuality;
  uint8          correlation;
  int8           rssi;
} ZMacDataCnf_t;


/* ASSOCIATION TYPES */

/* Associate request type */
typedef struct
{
  ZMacSec_t     Sec;
  uint8         LogicalChannel;
  uint8         ChannelPage;
  zAddrType_t   CoordAddress;
  uint16        CoordPANId;
  uint8         CapabilityFlags;
} ZMacAssociateReq_t;

/* Associate response type */
typedef struct
{
  ZMacSec_t      Sec;
  ZLongAddr_t    DeviceAddress;
  uint16         AssocShortAddress;
  uint8          Status;
} ZMacAssociateRsp_t;

/* Associate indication parameters type */
typedef struct
{
  ZMacEventHdr_t hdr;
  ZLongAddr_t    DeviceAddress;
  uint8          CapabilityFlags;
  ZMacSec_t      Sec;
} ZMacAssociateInd_t;

/* Associate confim type */
typedef struct
{
  ZMacEventHdr_t hdr;
  uint16         AssocShortAddress;
  ZMacSec_t      Sec;
} ZMacAssociateCnf_t;

/* Disassociate request type */
typedef struct
{
  ZMacSec_t     Sec;
  zAddrType_t   DeviceAddress;
  uint16        DevicePanId;
  uint8         DisassociateReason;
  uint8         TxIndirect;
} ZMacDisassociateReq_t;

/* Rx enable confirm type */
typedef struct
{
  ZMacEventHdr_t hdr;
} ZMacRxEnableCnf_t;

/* SCAN */
/* Scan request type */
typedef struct
{
  uint32         ScanChannels;
  uint8          ScanType;			
  uint8          ScanDuration;
  uint8          ChannelPage;
  uint8          MaxResults;
  /* Adding fields for enhanced active scan request */
  _Bool           PermitJoining;
  uint8          LinkQuality;
  uint8          PercentFilter;
  ZMacSec_t      Sec;
  union
  {
    uint8        *pEnergyDetect;
    ZMacPanDesc_t *pPanDescriptor;
  }Result;
} ZMacScanReq_t;

/* Scan confirm type */
typedef struct
{
  ZMacEventHdr_t hdr;
  uint8          ScanType;
  uint8          ChannelPage;
  uint32         UnscannedChannels;
  uint8          ResultListSize;
  union
  {
    uint8         *pEnergyDetect;
    ZMacPanDesc_t *pPanDescriptor;
  }Result;
} ZMacScanCnf_t;


/* START */
/* Start request type */
typedef struct
{
  uint32        StartTime;
  uint16        PANID;
  uint8         LogicalChannel;
  uint8         ChannelPage;
  uint8         BeaconOrder;
  uint8         SuperframeOrder;
  uint8         PANCoordinator;
  uint8         BatteryLifeExt;
  uint8         CoordRealignment;
  ZMacSec_t     RealignSec;
  ZMacSec_t     BeaconSec;
} ZMacStartReq_t;

/* Start confirm type */
typedef struct
{
  ZMacEventHdr_t hdr;
} ZMacStartCnf_t;

/* POLL */
/* Roll request type */
typedef struct
{
  zAddrType_t CoordAddress;
  uint16      CoordPanId;
  ZMacSec_t   Sec;
} ZMacPollReq_t;

/* Poll confirm type */
typedef struct
{
  ZMacEventHdr_t hdr;
} ZMacPollCnf_t;

/* MAC_MLME_POLL_IND type */
typedef struct
{
  ZMacEventHdr_t  hdr;
  sAddr_t         srcAddr;        /* Short address of the device sending the data request */
  uint16          srcPanId;       /* Pan ID of the device sending the data request */
  uint8           noRsp;          /* indication that no MAC_McpsDataReq() is required.
                                   * It is set when MAC_MLME_POLL_IND is generated,
                                   * to simply indicate that a received data request frame
                                   * was acked with pending bit cleared. */
} ZMacPollInd_t;

/* ORPHAN */
/* Orphan response type */
typedef struct
{
  ZMacSec_t      Sec;
  ZLongAddr_t    OrphanAddress;
  uint16         ShortAddress;
  uint8          AssociatedMember;
} ZMacOrphanRsp_t;

/* Orphan indication type */
typedef struct
{
  ZMacEventHdr_t hdr;
  ZLongAddr_t    OrphanAddress;
  ZMacSec_t      Sec;
} ZMacOrphanInd_t;

#line 417 "F:\\Workspace\\zstack_iar_zf\\Components\\zmac\\ZMAC.h"

typedef enum
{
  TX_PWR_MINUS_22 = -22,
  TX_PWR_MINUS_21,
  TX_PWR_MINUS_20,
  TX_PWR_MINUS_19,
  TX_PWR_MINUS_18,
  TX_PWR_MINUS_17,
  TX_PWR_MINUS_16,
  TX_PWR_MINUS_15,
  TX_PWR_MINUS_14,
  TX_PWR_MINUS_13,
  TX_PWR_MINUS_12,
  TX_PWR_MINUS_11,
  TX_PWR_MINUS_10,
  TX_PWR_MINUS_9,
  TX_PWR_MINUS_8,
  TX_PWR_MINUS_7,
  TX_PWR_MINUS_6,
  TX_PWR_MINUS_5,
  TX_PWR_MINUS_4,
  TX_PWR_MINUS_3,
  TX_PWR_MINUS_2,
  TX_PWR_MINUS_1,
  TX_PWR_ZERO,
  TX_PWR_PLUS_1,
  TX_PWR_PLUS_2,
  TX_PWR_PLUS_3,
  TX_PWR_PLUS_4,
  TX_PWR_PLUS_5,
  TX_PWR_PLUS_6,
  TX_PWR_PLUS_7,
  TX_PWR_PLUS_8,
  TX_PWR_PLUS_9,
  TX_PWR_PLUS_10,
  TX_PWR_PLUS_11,
  TX_PWR_PLUS_12,
  TX_PWR_PLUS_13,
  TX_PWR_PLUS_14,
  TX_PWR_PLUS_15,
  TX_PWR_PLUS_16,
  TX_PWR_PLUS_17,
  TX_PWR_PLUS_18,
  TX_PWR_PLUS_19
} ZMacTransmitPower_t;  // The transmit power in units of -1 dBm.

typedef struct
{
  byte protocolID;
  byte stackProfile;    // 4 bit in native
  byte protocolVersion; // 4 bit in native
  byte reserved;        // 2 bit in native
  byte routerCapacity;  // 1 bit in native
  byte deviceDepth;     // 4 bit in native
  byte deviceCapacity;  // 1 bit in native
  byte extendedPANID[8];
  byte txOffset[3];
  byte updateId;
} beaconPayload_t;

typedef uint8 (*applySecCB_t)( uint8 len, uint8 *msdu );

typedef enum
{
  LQI_ADJ_OFF = 0,
  LQI_ADJ_MODE1,
  LQI_ADJ_MODE2,
  LQI_ADJ_GET = 0xFF
} ZMacLqiAdjust_t;  // Mode settings for lqi adjustment

/*********************************************************************
 * GLOBAL VARIABLES
 */


/*********************************************************************
 * FUNCTIONS
 */

  /*
   * Initialize.
   */
  extern ZMacStatus_t ZMacInit( void );

  /*
   * Send a MAC Data Frame packet.
   */
  extern ZMacStatus_t ZMacDataReq( ZMacDataReq_t *param );

  /*
   * Send a MAC Data Frame packet and apply application security to the packet.
   */
  extern uint8 ZMacDataReqSec( ZMacDataReq_t *pData, applySecCB_t secCB );

  /*
   * Request an association with a coordinator.
   */
  extern ZMacStatus_t ZMacAssociateReq( ZMacAssociateReq_t *param );

  /*
   * Request to send an association response message.
   */
  extern ZMacStatus_t ZMacAssociateRsp( ZMacAssociateRsp_t *param );

  /*
   * Request to send a disassociate request message.
   */
  extern ZMacStatus_t ZMacDisassociateReq( ZMacDisassociateReq_t *param );

  /*
   * Gives the MAC extra processing time.
   * Returns false if its OK to sleep.
   */
  extern byte ZMacUpdate( void );

  /*
   * Read a MAC PIB attribute.
   */
  extern ZMacStatus_t ZMacGetReq( ZMacAttributes_t attr, byte *value );

  /*
   * This function allows the next higher layer to respond to
   * an orphan indication message.
   */
  extern ZMacStatus_t ZMacOrphanRsp( ZMacOrphanRsp_t *param );

  /*
   * This function is called to request MAC data request poll.
   */
  extern ZMacStatus_t ZMacPollReq( ZMacPollReq_t *param );

  /*
   * Reset the MAC.
   */
  extern ZMacStatus_t ZMacReset( byte SetDefaultPIB );

  /*
   * This function is called to perform a network scan.
   */
  extern ZMacStatus_t ZMacScanReq( ZMacScanReq_t *param );

  /*
   * Write a MAC PIB attribute.
   */
  extern ZMacStatus_t ZMacSetReq( ZMacAttributes_t attr, byte *value );

#line 575 "F:\\Workspace\\zstack_iar_zf\\Components\\zmac\\ZMAC.h"

  /*
   * This function is called to tell the MAC to transmit beacons
   * and become a coordinator.
   */
  extern ZMacStatus_t ZMacStartReq( ZMacStartReq_t *param );

  /*
   * This function is called to request a sync to the current
   * networks beacons.
   */
  extern ZMacStatus_t ZMacSyncReq( ZMacSyncReq_t *param );

  /*
   * This function requests to reset mac state machine and
   * transaction.
   */
  extern ZMacStatus_t ZMacCleanReq( void );

  /*
   * This function is called to request MAC to purge a message.
   */
  extern ZMacStatus_t ZMacPurgeReq( byte msduHandle );

  /*
   * This function is called to enable AUTOPEND and source address matching.
   */
  extern ZMacStatus_t ZMacSrcMatchEnable ( void );

 /*
  * This function is called to add a short or extended address to source address table.
  */
  extern ZMacStatus_t ZMacSrcMatchAddEntry (zAddrType_t *addr, uint16 panID);

  /*
   * This function is called to delete a short or extended address from source address table.
   */
  extern ZMacStatus_t ZMacSrcMatchDeleteEntry (zAddrType_t *addr, uint16 panID);

  /*
   * This funciton is called to enabled/disable acknowledging all packets with pending bit set
   */
  extern ZMacStatus_t ZMacSrcMatchAckAllPending (uint8 option);

  /*
   * This function is called to check if acknowledging all packets with pending bit set is enabled.
   */
  extern ZMacStatus_t ZMacSrcMatchCheckAllPending (void);

  /*
   * This function is called to request MAC to power on the radio hardware and wake up.
   */
  extern void ZMacPwrOnReq ( void );

  /*
   * This function returns the current power mode of the MAC.
   */
  extern uint8 ZMac_PwrMode(void);

  /*
   * This function is called to request MAC to set the transmit power level.
   */
  extern ZMacStatus_t ZMacSetTransmitPower( ZMacTransmitPower_t level );

  /*
   * This function is called to send out an empty msg
   */
  extern void ZMacSendNoData( uint16 DstAddr, uint16 DstPANId );

  /*
   * This callback function is called for every MAC message that is received
   * over-the-air or generated locally by MAC for the application.
   */
  extern uint8 (*pZMac_AppCallback)( uint8 *msgPtr );

  /*
   * This function returns true if the MAC state is idle.
   */
  extern uint8 ZMacStateIdle( void );

  /*
   * This function sets/returns LQI adjust mode.
   */
  extern ZMacLqiAdjust_t ZMacLqiAdjustMode( ZMacLqiAdjust_t mode );

  /*
   * This function sends out an enhanced active scan request
   */
  extern ZMacStatus_t ZMacEnhancedActiveScanReq( ZMacScanReq_t *param );

#line 688 "F:\\Workspace\\zstack_iar_zf\\Components\\zmac\\ZMAC.h"

/*********************************************************************
*********************************************************************/





#line 53 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\nwk\\nwk.h"
#line 1 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\nwk\\nwk_bufs.h"
/**************************************************************************************************
  Filename:       nwk_bufs.h
  Revised:        $Date: 2014-11-18 02:32:26 -0800 (Tue, 18 Nov 2014) $
  Revision:       $Revision: 41160 $

  Description:    Network buffer utility functions.


  Copyright 2004-2014 Texas Instruments Incorporated. All rights reserved.

  IMPORTANT: Your use of this Software is limited to those specific rights
  granted under the terms of a software license agreement between the user
  who downloaded the software, his/her employer (which must be your employer)
  and Texas Instruments Incorporated (the "License").  You may not use this
  Software unless you agree to abide by the terms of the License. The License
  limits your use, and you acknowledge, that the Software may not be modified,
  copied or distributed unless embedded on a Texas Instruments microcontroller
  or used solely and exclusively in conjunction with a Texas Instruments radio
  frequency transceiver, which is integrated into your product.  Other than for
  the foregoing purpose, you may not use, reproduce, copy, prepare derivative
  works of, modify, distribute, perform, display or sell this Software and/or
  its documentation for any purpose.

  YOU FURTHER ACKNOWLEDGE AND AGREE THAT THE SOFTWARE AND DOCUMENTATION ARE
  PROVIDED "AS IS" WITHOUT WARRANTY OF ANY KIND, EITHER EXPRESS OR IMPLIED,
  INCLUDING WITHOUT LIMITATION, ANY WARRANTY OF MERCHANTABILITY, TITLE,
  NON-INFRINGEMENT AND FITNESS FOR A PARTICULAR PURPOSE. IN NO EVENT SHALL
  TEXAS INSTRUMENTS OR ITS LICENSORS BE LIABLE OR OBLIGATED UNDER CONTRACT,
  NEGLIGENCE, STRICT LIABILITY, CONTRIBUTION, BREACH OF WARRANTY, OR OTHER
  LEGAL EQUITABLE THEORY ANY DIRECT OR INDIRECT DAMAGES OR EXPENSES
  INCLUDING BUT NOT LIMITED TO ANY INCIDENTAL, SPECIAL, INDIRECT, PUNITIVE
  OR CONSEQUENTIAL DAMAGES, LOST PROFITS OR LOST DATA, COST OF PROCUREMENT
  OF SUBSTITUTE GOODS, TECHNOLOGY, SERVICES, OR ANY CLAIMS BY THIRD PARTIES
  (INCLUDING BUT NOT LIMITED TO ANY DEFENSE THEREOF), OR OTHER SIMILAR COSTS.

  Should you have any questions regarding your right to use this Software,
  contact Texas Instruments Incorporated at www.TI.com.
**************************************************************************************************/








/*********************************************************************
 * INCLUDES
 */




/*********************************************************************
 * MACROS
 */

/*********************************************************************
 * CONSTANTS
 */
// Data buffer queue states
#line 69 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\nwk\\nwk_bufs.h"

// Handle options
#line 78 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\nwk\\nwk_bufs.h"
//#define HANDLE_DIRECT             0x0040
#line 88 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\nwk\\nwk_bufs.h"

/*********************************************************************
 * TYPEDEFS
 */
typedef struct
{
  uint8 type;
  uint16 txOptions;
  void* load;
} nwkDB_UserData_t;

typedef struct
{
  ZMacDataReq_t *pDataReq;
  void *next;
  uint16 dataX;
  uint16 handleOptions;     // Packet type options
  uint8 nsduHandle;         // unique ID
  uint8 state;              // state of buffer
  uint8 retries;            // number of APS retries
  uint8 lastCnfStatus;      // The last MAC_MCPS_DATA_CNF status
  nwkDB_UserData_t ud;      // user data
  uint16 macSrcAddr;        // original MAC src address
  uint8  apsRetries;        // Number of retries by APS layer
} nwkDB_t;

typedef uint8 (*nwkDB_FindMatchCB_t)( nwkDB_t* db, void* mf );

/*********************************************************************
 * GLOBAL VARIABLES
 */

/*********************************************************************
 * FUNCTIONS
 */

/*
 * Variable initialization
 */
extern void nwkbufs_init( void );

/*
 * Send the next buffer
 */
extern void nwk_SendNextDataBuf( void );

/*
 * Delete all buffers for a device
 */
extern uint8 nwk_DeleteDataBufs( uint16 nwkAddr );

/*
 * Determines whether or not the data buffers are full.
 */
extern byte nwk_MacDataBuffersFull( void );

/*
 * Add buffer to the send queue, if already in queue - set
 */
extern uint8 nwk_MacDataBuffersAdd( nwkDB_t* db, uint8 sent );

/*
 * Deallocate the sent MAC Data Buffer
 *
 */
extern uint8 nwk_MacDataBuffersDealloc( byte handle );

/*
 * Checks if an end device has a message pending in the MAC NP.
 */
extern uint8 nwkDB_MaxIndirectSent( uint16 addr );


/*********************************************************************
*  Queued Allocated functions
*/

/*
 * Create the header
 */
extern nwkDB_t *nwkDB_CreateHdr( ZMacDataReq_t *pkt, byte handle, uint16 handleOptions );

/*
 * Add a buffer to the queue.
 */
extern ZStatus_t nwkDB_Add( nwkDB_t *pkt, byte type, uint16 dataX );

/*
 * Find the number of buffers with type.
 */
extern byte nwkDB_CountTypes( byte type );

/*
 * Find the next type in list.
 */
extern nwkDB_t *nwkDB_FindNextType( nwkDB_t *pkt, byte type, byte direct );

/*
 * Find the rec with handle.
 */
extern nwkDB_t *nwkDB_FindHandle( byte handle );

/*
 * Find the rec with destination address.
 */
extern nwkDB_t *nwkDB_FindDstAddr( uint16 addr );

/*
 * Find the rec with MAC data packet.
 */
extern nwkDB_t *nwkDB_FindDataPkt( ZMacDataReq_t *pkt );

/*
 * Find a buffer match.
 */
extern nwkDB_t* nwkDB_FindMatch( nwkDB_FindMatchCB_t cb, void* mf );

/*
 * Find and remove from the list.  This function doesn't
 *           free the memory used by the record.
 */
extern void nwkDB_RemoveFromList( nwkDB_t *pkt );

/*
 * Frees the data, mac packet and hdr
 */
extern void nwkDB_DeleteRecAll( nwkDB_t *rec );

/*
 * Setup hold state and timer tick.
 */
extern void nwkbufs_hold( nwkDB_t *rec );

/*
 * Return cntIndirectHolding
 */
extern uint8 nwkDB_ReturnIndirectHoldingCnt( void );

/*
 * Count Indirect held message
 */
extern uint8 nwkDB_CountIndirectHold( void );

/*
 * Delete all records and reset queue
 */
extern void nwkbufs_reset( void );

/*
 * Stub to load the user frame data
 */
extern void* nwkDB_UserDataLoad( nwkDB_UserData_t* ud );

/*********************************************************************
*  Broadcast Message Queue functions
*/

/*
 * Add a broadcast data indication to the network broadcast queue
 */
extern uint8 nwk_broadcastSend( uint8 *msg_ptr );

/*
 * Remove a broadcast data indication to the network broadcast queue
 */
extern uint8 *nwk_broadcastReceive( void );

/*********************************************************************
*********************************************************************/







#line 54 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\nwk\\nwk.h"
#line 1 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\nwk\\NLMEDE.h"
/**************************************************************************************************
  Filename:       NLMEDE.h
  Revised:        $Date: 2015-06-02 15:55:43 -0700 (Tue, 02 Jun 2015) $
  Revision:       $Revision: 43961 $

  Description:    Network layer interface NLME and NLDE.


  Copyright 2004-2015 Texas Instruments Incorporated. All rights reserved.

  IMPORTANT: Your use of this Software is limited to those specific rights
  granted under the terms of a software license agreement between the user
  who downloaded the software, his/her employer (which must be your employer)
  and Texas Instruments Incorporated (the "License").  You may not use this
  Software unless you agree to abide by the terms of the License. The License
  limits your use, and you acknowledge, that the Software may not be modified,
  copied or distributed unless embedded on a Texas Instruments microcontroller
  or used solely and exclusively in conjunction with a Texas Instruments radio
  frequency transceiver, which is integrated into your product.  Other than for
  the foregoing purpose, you may not use, reproduce, copy, prepare derivative
  works of, modify, distribute, perform, display or sell this Software and/or
  its documentation for any purpose.

  YOU FURTHER ACKNOWLEDGE AND AGREE THAT THE SOFTWARE AND DOCUMENTATION ARE
  PROVIDED "AS IS" WITHOUT WARRANTY OF ANY KIND, EITHER EXPRESS OR IMPLIED,
  INCLUDING WITHOUT LIMITATION, ANY WARRANTY OF MERCHANTABILITY, TITLE,
  NON-INFRINGEMENT AND FITNESS FOR A PARTICULAR PURPOSE. IN NO EVENT SHALL
  TEXAS INSTRUMENTS OR ITS LICENSORS BE LIABLE OR OBLIGATED UNDER CONTRACT,
  NEGLIGENCE, STRICT LIABILITY, CONTRIBUTION, BREACH OF WARRANTY, OR OTHER
  LEGAL EQUITABLE THEORY ANY DIRECT OR INDIRECT DAMAGES OR EXPENSES
  INCLUDING BUT NOT LIMITED TO ANY INCIDENTAL, SPECIAL, INDIRECT, PUNITIVE
  OR CONSEQUENTIAL DAMAGES, LOST PROFITS OR LOST DATA, COST OF PROCUREMENT
  OF SUBSTITUTE GOODS, TECHNOLOGY, SERVICES, OR ANY CLAIMS BY THIRD PARTIES
  (INCLUDING BUT NOT LIMITED TO ANY DEFENSE THEREOF), OR OTHER SIMILAR COSTS.

  Should you have any questions regarding your right to use this Software,
  contact Texas Instruments Incorporated at www.TI.com.
**************************************************************************************************/








/*********************************************************************
 * INCLUDES
 */
#line 1 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\nwk\\AssocList.h"
/**************************************************************************************************
  Filename:       AssocList.h
  Revised:        $Date: 2015-01-22 13:22:52 -0800 (Thu, 22 Jan 2015) $
  Revision:       $Revision: 41965 $

  Description:    Associated Device List.


  Copyright 2004-2015 Texas Instruments Incorporated. All rights reserved.

  IMPORTANT: Your use of this Software is limited to those specific rights
  granted under the terms of a software license agreement between the user
  who downloaded the software, his/her employer (which must be your employer)
  and Texas Instruments Incorporated (the "License").  You may not use this
  Software unless you agree to abide by the terms of the License. The License
  limits your use, and you acknowledge, that the Software may not be modified,
  copied or distributed unless embedded on a Texas Instruments microcontroller
  or used solely and exclusively in conjunction with a Texas Instruments radio
  frequency transceiver, which is integrated into your product.  Other than for
  the foregoing purpose, you may not use, reproduce, copy, prepare derivative
  works of, modify, distribute, perform, display or sell this Software and/or
  its documentation for any purpose.

  YOU FURTHER ACKNOWLEDGE AND AGREE THAT THE SOFTWARE AND DOCUMENTATION ARE
  PROVIDED “AS IS” WITHOUT WARRANTY OF ANY KIND, EITHER EXPRESS OR IMPLIED,
  INCLUDING WITHOUT LIMITATION, ANY WARRANTY OF MERCHANTABILITY, TITLE,
  NON-INFRINGEMENT AND FITNESS FOR A PARTICULAR PURPOSE. IN NO EVENT SHALL
  TEXAS INSTRUMENTS OR ITS LICENSORS BE LIABLE OR OBLIGATED UNDER CONTRACT,
  NEGLIGENCE, STRICT LIABILITY, CONTRIBUTION, BREACH OF WARRANTY, OR OTHER
  LEGAL EQUITABLE THEORY ANY DIRECT OR INDIRECT DAMAGES OR EXPENSES
  INCLUDING BUT NOT LIMITED TO ANY INCIDENTAL, SPECIAL, INDIRECT, PUNITIVE
  OR CONSEQUENTIAL DAMAGES, LOST PROFITS OR LOST DATA, COST OF PROCUREMENT
  OF SUBSTITUTE GOODS, TECHNOLOGY, SERVICES, OR ANY CLAIMS BY THIRD PARTIES
  (INCLUDING BUT NOT LIMITED TO ANY DEFENSE THEREOF), OR OTHER SIMILAR COSTS.

  Should you have any questions regarding your right to use this Software,
  contact Texas Instruments Incorporated at www.TI.com.
**************************************************************************************************/








/*********************************************************************
 * INCLUDES
 */

#line 1 "F:\\Workspace\\zstack_iar_zf\\Components\\osal\\include\\OSAL.h"
/******************************************************************************
  Filename:     OSAL.h
  Revised:      $Date: 2014-06-30 16:38:56 -0700 (Mon, 30 Jun 2014) $
  Revision:     $Revision: 39297 $

  Description:  This API allows the software components in the Z-Stack to be
                written independently of the specifics of the operating system,
                kernel, or tasking environment (including control loops or
                connect-to-interrupt systems).


  Copyright 2004-2014 Texas Instruments Incorporated. All rights reserved.

  IMPORTANT: Your use of this Software is limited to those specific rights
  granted under the terms of a software license agreement between the user
  who downloaded the software, his/her employer (which must be your employer)
  and Texas Instruments Incorporated (the "License").  You may not use this
  Software unless you agree to abide by the terms of the License. The License
  limits your use, and you acknowledge, that the Software may not be modified,
  copied or distributed unless embedded on a Texas Instruments microcontroller
  or used solely and exclusively in conjunction with a Texas Instruments radio
  frequency transceiver, which is integrated into your product. Other than for
  the foregoing purpose, you may not use, reproduce, copy, prepare derivative
  works of, modify, distribute, perform, display or sell this Software and/or
  its documentation for any purpose.

  YOU FURTHER ACKNOWLEDGE AND AGREE THAT THE SOFTWARE AND DOCUMENTATION ARE
  PROVIDED “AS IS” WITHOUT WARRANTY OF ANY KIND, EITHER EXPRESS OR IMPLIED,
  INCLUDING WITHOUT LIMITATION, ANY WARRANTY OF MERCHANTABILITY, TITLE,
  NON-INFRINGEMENT AND FITNESS FOR A PARTICULAR PURPOSE. IN NO EVENT SHALL
  TEXAS INSTRUMENTS OR ITS LICENSORS BE LIABLE OR OBLIGATED UNDER CONTRACT,
  NEGLIGENCE, STRICT LIABILITY, CONTRIBUTION, BREACH OF WARRANTY, OR OTHER
  LEGAL EQUITABLE THEORY ANY DIRECT OR INDIRECT DAMAGES OR EXPENSES
  INCLUDING BUT NOT LIMITED TO ANY INCIDENTAL, SPECIAL, INDIRECT, PUNITIVE
  OR CONSEQUENTIAL DAMAGES, LOST PROFITS OR LOST DATA, COST OF PROCUREMENT
  OF SUBSTITUTE GOODS, TECHNOLOGY, SERVICES, OR ANY CLAIMS BY THIRD PARTIES
  (INCLUDING BUT NOT LIMITED TO ANY DEFENSE THEREOF), OR OTHER SIMILAR COSTS.

  Should you have any questions regarding your right to use this Software,
  contact Texas Instruments Incorporated at www.TI.com.
******************************************************************************/









/*********************************************************************
 * INCLUDES
 */

#line 1 "F:\\Workspace\\frama-c\\frama-c-master\\share\\libc\\limits.h"
/**************************************************************************/
/*                                                                        */
/*  This file is part of Frama-C.                                         */
/*                                                                        */
/*  Copyright (C) 2007-2022                                               */
/*    CEA (Commissariat Ã  l'Ã©nergie atomique et aux Ã©nergies              */
/*         alternatives)                                                  */
/*                                                                        */
/*  you can redistribute it and/or modify it under the terms of the GNU   */
/*  Lesser General Public License as published by the Free Software       */
/*  Foundation, version 2.1.                                              */
/*                                                                        */
/*  It is distributed in the hope that it will be useful,                 */
/*  but WITHOUT ANY WARRANTY; without even the implied warranty of        */
/*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         */
/*  GNU Lesser General Public License for more details.                   */
/*                                                                        */
/*  See the GNU Lesser General Public License version 2.1                 */
/*  for more details (enclosed in the file licenses/LGPLv2.1).            */
/*                                                                        */
/**************************************************************************/

/* ISO C: 7.10 and 5.2.4.2.1 */



#line 1 "F:\\Workspace\\frama-c\\frama-c-master\\share\\libc\\__fc_machdep.h"
/**************************************************************************/
/*                                                                        */
/*  This file is part of Frama-C.                                         */
/*                                                                        */
/*  Copyright (C) 2007-2022                                               */
/*    CEA (Commissariat Ã  l'Ã©nergie atomique et aux Ã©nergies              */
/*         alternatives)                                                  */
/*                                                                        */
/*  you can redistribute it and/or modify it under the terms of the GNU   */
/*  Lesser General Public License as published by the Free Software       */
/*  Foundation, version 2.1.                                              */
/*                                                                        */
/*  It is distributed in the hope that it will be useful,                 */
/*  but WITHOUT ANY WARRANTY; without even the implied warranty of        */
/*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         */
/*  GNU Lesser General Public License for more details.                   */
/*                                                                        */
/*  See the GNU Lesser General Public License version 2.1                 */
/*  for more details (enclosed in the file licenses/LGPLv2.1).            */
/*                                                                        */
/**************************************************************************/




#line 1 "F:\\Workspace\\frama-c\\frama-c-master\\share\\libc\\__fc_machdep_linux_shared.h"
/**************************************************************************/
/*                                                                        */
/*  This file is part of Frama-C.                                         */
/*                                                                        */
/*  Copyright (C) 2007-2022                                               */
/*    CEA (Commissariat Ã  l'Ã©nergie atomique et aux Ã©nergies              */
/*         alternatives)                                                  */
/*                                                                        */
/*  you can redistribute it and/or modify it under the terms of the GNU   */
/*  Lesser General Public License as published by the Free Software       */
/*  Foundation, version 2.1.                                              */
/*                                                                        */
/*  It is distributed in the hope that it will be useful,                 */
/*  but WITHOUT ANY WARRANTY; without even the implied warranty of        */
/*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         */
/*  GNU Lesser General Public License for more details.                   */
/*                                                                        */
/*  See the GNU Lesser General Public License version 2.1                 */
/*  for more details (enclosed in the file licenses/LGPLv2.1).            */
/*                                                                        */
/**************************************************************************/




/* This file contains common machine specific values between 
   Linux x86 32-bit, AMD64 and x86 16-bit.*/




// These machdeps strive to conform themselves to POSIX.1-2008


/* Optional */














/* inttypes */




/* Required */














/* Required */















/* Required */





/* min and max values as specified in limits.h */
#line 103 "F:\\Workspace\\frama-c\\frama-c-master\\share\\libc\\__fc_machdep_linux_shared.h"
// Note: POSIX requires HOST_NAME_MAX >= 255, but Linux uses 64



/* for stdarg.h */


/* stdint.h */
/* NB: in signal.h, sig_atomic_t is hardwired to int. */
#line 119 "F:\\Workspace\\frama-c\\frama-c-master\\share\\libc\\__fc_machdep_linux_shared.h"

// Linux usually defines wchar_t as a signed int, but this is not required


/* stdio.h */
#line 130 "F:\\Workspace\\frama-c\\frama-c-master\\share\\libc\\__fc_machdep_linux_shared.h"

/* stdlib.h */



/* errno.h */
#line 270 "F:\\Workspace\\frama-c\\frama-c-master\\share\\libc\\__fc_machdep_linux_shared.h"

/* time.h */


/* signal.h */



#line 29 "F:\\Workspace\\frama-c\\frama-c-master\\share\\libc\\__fc_machdep.h"


/* Required */
#line 48 "F:\\Workspace\\frama-c\\frama-c-master\\share\\libc\\__fc_machdep.h"

/* Optional */












/* prefixes for inttypes */




/* Required */




























/* POSIX */


/* stdio.h */



/* stdint.h */


/* wchar.h */









// End of X86_32 || GCC_X86_32
#line 28 "F:\\Workspace\\frama-c\\frama-c-master\\share\\libc\\limits.h"

/* Number of bits in a `char'.	*/



/* Minimum and maximum values a `signed char' can hold.  */



/* Maximum value an `unsigned char' can hold.  (Minimum is 0.)  */


/* Minimum and maximum values a `char' can hold.  */
#line 48 "F:\\Workspace\\frama-c\\frama-c-master\\share\\libc\\limits.h"



/* Minimum and maximum values a `signed short int' can hold.  */



/* Maximum value an `unsigned short int' can hold.  (Minimum is 0.)  */


/* Minimum and maximum values a `signed int' can hold.  */



/* Maximum value an `unsigned int' can hold.  (Minimum is 0.)  */


/* Minimum and maximum values a `signed long int' can hold.  */



/* Maximum value an `unsigned long int' can hold.  (Minimum is 0.)  */


/* Minimum and maximum values a `signed long long int' can hold.  */



/* Maximum value an `unsigned long long int' can hold.  (Minimum is 0.)  */


/* Maximum number of bytes in a pathname, including the terminating
   null character. (Minimum is 256.) */


/* Maximum length of a host name (not including the terminating null)
   as returned from the gethostname() function.
   Note: Mac OS does not define this constant. */


/* Maximum length of a terminal device name. */


/* Maximum length of argument to the exec functions including environment data.
   Minimum Acceptable Value: {_POSIX_ARG_MAX} (4096 in POSIX.1-2008)
   "... the total space used to store the environment and the arguments to the
    process is limited to {ARG_MAX} bytes."
 */


// POSIX; used by <sys/uio.h>.
// Must be >= _XOPEN_IOV_MAX, which is 16.
// 1024 is the value used by some Linux implementations.



// Maximum Values



// Minimum Values

#line 159 "F:\\Workspace\\frama-c\\frama-c-master\\share\\libc\\limits.h"

// Other Invariant Values

#line 168 "F:\\Workspace\\frama-c\\frama-c-master\\share\\libc\\limits.h"

#line 56 "F:\\Workspace\\zstack_iar_zf\\Components\\osal\\include\\OSAL.h"

#line 1 "F:\\Workspace\\zstack_iar_zf\\Components\\osal\\include\\OSAL_Memory.h"
/**************************************************************************************************
  Filename:       OSAL_Memory.h
  Revised:        $Date: 2010-07-28 08:42:48 -0700 (Wed, 28 Jul 2010) $
  Revision:       $Revision: 23160 $
    
  Description:    This module defines the OSAL memory control functions. 
    
            
  Copyright 2004-2007 Texas Instruments Incorporated. All rights reserved.

  IMPORTANT: Your use of this Software is limited to those specific rights
  granted under the terms of a software license agreement between the user
  who downloaded the software, his/her employer (which must be your employer)
  and Texas Instruments Incorporated (the "License").  You may not use this
  Software unless you agree to abide by the terms of the License. The License
  limits your use, and you acknowledge, that the Software may not be modified,
  copied or distributed unless embedded on a Texas Instruments microcontroller
  or used solely and exclusively in conjunction with a Texas Instruments radio
  frequency transceiver, which is integrated into your product.  Other than for
  the foregoing purpose, you may not use, reproduce, copy, prepare derivative
  works of, modify, distribute, perform, display or sell this Software and/or
  its documentation for any purpose.

  YOU FURTHER ACKNOWLEDGE AND AGREE THAT THE SOFTWARE AND DOCUMENTATION ARE
  PROVIDED “AS IS” WITHOUT WARRANTY OF ANY KIND, EITHER EXPRESS OR IMPLIED, 
  INCLUDING WITHOUT LIMITATION, ANY WARRANTY OF MERCHANTABILITY, TITLE, 
  NON-INFRINGEMENT AND FITNESS FOR A PARTICULAR PURPOSE. IN NO EVENT SHALL
  TEXAS INSTRUMENTS OR ITS LICENSORS BE LIABLE OR OBLIGATED UNDER CONTRACT,
  NEGLIGENCE, STRICT LIABILITY, CONTRIBUTION, BREACH OF WARRANTY, OR OTHER
  LEGAL EQUITABLE THEORY ANY DIRECT OR INDIRECT DAMAGES OR EXPENSES
  INCLUDING BUT NOT LIMITED TO ANY INCIDENTAL, SPECIAL, INDIRECT, PUNITIVE
  OR CONSEQUENTIAL DAMAGES, LOST PROFITS OR LOST DATA, COST OF PROCUREMENT
  OF SUBSTITUTE GOODS, TECHNOLOGY, SERVICES, OR ANY CLAIMS BY THIRD PARTIES
  (INCLUDING BUT NOT LIMITED TO ANY DEFENSE THEREOF), OR OTHER SIMILAR COSTS.

  Should you have any questions regarding your right to use this Software,
  contact Texas Instruments Incorporated at www.TI.com. 
**************************************************************************************************/









/*********************************************************************
 * INCLUDES
 */

 
/*********************************************************************
 * CONSTANTS
 */





/*********************************************************************
 * MACROS
 */
  


/*********************************************************************
 * TYPEDEFS
 */

/*********************************************************************
 * GLOBAL VARIABLES
 */
 
/*********************************************************************
 * FUNCTIONS
 */

 /*
  * Initialize memory manager.
  */
  void osal_mem_init( void );

 /*
  * Setup efficient search for the first free block of heap.
  */
  void osal_mem_kick( void );

 /*
  * Allocate a block of memory.
  */




  void *osal_mem_alloc( uint16 size );


 /*
  * Free a block of memory.
  */




  void osal_mem_free( void *ptr );


#line 130 "F:\\Workspace\\zstack_iar_zf\\Components\\osal\\include\\OSAL_Memory.h"

#line 137 "F:\\Workspace\\zstack_iar_zf\\Components\\osal\\include\\OSAL_Memory.h"

/*********************************************************************
*********************************************************************/





#line 59 "F:\\Workspace\\zstack_iar_zf\\Components\\osal\\include\\OSAL.h"
#line 1 "F:\\Workspace\\zstack_iar_zf\\Components\\osal\\include\\OSAL_Timers.h"
/**************************************************************************************************
  Filename:       OSAL_Timers.h
  Revised:        $Date: 2011-09-16 19:09:24 -0700 (Fri, 16 Sep 2011) $
  Revision:       $Revision: 27618 $

  Description:    This file contains the OSAL Timer definition and manipulation functions.


  Copyright 2004-2009 Texas Instruments Incorporated. All rights reserved.

  IMPORTANT: Your use of this Software is limited to those specific rights
  granted under the terms of a software license agreement between the user
  who downloaded the software, his/her employer (which must be your employer)
  and Texas Instruments Incorporated (the "License").  You may not use this
  Software unless you agree to abide by the terms of the License. The License
  limits your use, and you acknowledge, that the Software may not be modified,
  copied or distributed unless embedded on a Texas Instruments microcontroller
  or used solely and exclusively in conjunction with a Texas Instruments radio
  frequency transceiver, which is integrated into your product.  Other than for
  the foregoing purpose, you may not use, reproduce, copy, prepare derivative
  works of, modify, distribute, perform, display or sell this Software and/or
  its documentation for any purpose.

  YOU FURTHER ACKNOWLEDGE AND AGREE THAT THE SOFTWARE AND DOCUMENTATION ARE
  PROVIDED “AS IS” WITHOUT WARRANTY OF ANY KIND, EITHER EXPRESS OR IMPLIED, 
  INCLUDING WITHOUT LIMITATION, ANY WARRANTY OF MERCHANTABILITY, TITLE, 
  NON-INFRINGEMENT AND FITNESS FOR A PARTICULAR PURPOSE. IN NO EVENT SHALL
  TEXAS INSTRUMENTS OR ITS LICENSORS BE LIABLE OR OBLIGATED UNDER CONTRACT,
  NEGLIGENCE, STRICT LIABILITY, CONTRIBUTION, BREACH OF WARRANTY, OR OTHER
  LEGAL EQUITABLE THEORY ANY DIRECT OR INDIRECT DAMAGES OR EXPENSES
  INCLUDING BUT NOT LIMITED TO ANY INCIDENTAL, SPECIAL, INDIRECT, PUNITIVE
  OR CONSEQUENTIAL DAMAGES, LOST PROFITS OR LOST DATA, COST OF PROCUREMENT
  OF SUBSTITUTE GOODS, TECHNOLOGY, SERVICES, OR ANY CLAIMS BY THIRD PARTIES
  (INCLUDING BUT NOT LIMITED TO ANY DEFENSE THEREOF), OR OTHER SIMILAR COSTS.

  Should you have any questions regarding your right to use this Software,
  contact Texas Instruments Incorporated at www.TI.com. 
**************************************************************************************************/









/*********************************************************************
 * INCLUDES
 */

/*********************************************************************
 * MACROS
 */

/*********************************************************************
 * CONSTANTS
 * the unit is chosen such that the 320us tick equivalent can fit in 
 * 32 bits.
 */


/*********************************************************************
 * TYPEDEFS
 */

/*********************************************************************
 * GLOBAL VARIABLES
 */

/*********************************************************************
 * FUNCTIONS
 */

  /*
   * Initialization for the OSAL Timer System.
   */
  extern void osalTimerInit( void );

  /*
   * Set a Timer
   */
  extern uint8 osal_start_timerEx( uint8 task_id, uint16 event_id, uint32 timeout_value );
  
  /*
   * Set a timer that reloads itself.
   */
  extern uint8 osal_start_reload_timer( uint8 taskID, uint16 event_id, uint32 timeout_value );

  /*
   * Stop a Timer
   */
  extern uint8 osal_stop_timerEx( uint8 task_id, uint16 event_id );

  /*
   * Get the tick count of a Timer.
   */
  extern uint32 osal_get_timeoutEx( uint8 task_id, uint16 event_id );

  /*
   * Simulated Timer Interrupt Service Routine
   */

  extern void osal_timer_ISR( void );

  /*
   * Adjust timer tables
   */
  extern void osal_adjust_timers( void );

  /*
   * Update timer tables
   */
  extern void osalTimerUpdate( uint32 updateTime );

  /*
   * Count active timers
   */
  extern uint8 osal_timer_num_active( void );

  /*
   * Set the hardware timer interrupts for sleep mode.
   * These functions should only be called in OSAL_PwrMgr.c
   */
  extern void osal_sleep_timers( void );
  extern void osal_unsleep_timers( void );

 /*
  * Read the system clock - returns milliseconds
  */
  extern uint32 osal_GetSystemClock( void );

  /*
   * Get the next OSAL timer expiration.
   * This function should only be called in OSAL_PwrMgr.c
   */
  extern uint32 osal_next_timeout( void );

/*********************************************************************
*********************************************************************/





#line 60 "F:\\Workspace\\zstack_iar_zf\\Components\\osal\\include\\OSAL.h"





/*********************************************************************
 * MACROS
 */


















/*********************************************************************
 * CONSTANTS
 */

/*** Interrupts ***/


/*********************************************************************
 * TYPEDEFS
 */



typedef struct
{
  void   *next;





  uint16 len;
  uint8  dest_id;
} osal_msg_hdr_t;


typedef struct
{
  uint8  event;
  uint8  status;
} osal_event_hdr_t;

typedef void * osal_msg_q_t;






/*********************************************************************
 * GLOBAL VARIABLES
 */
#line 134 "F:\\Workspace\\zstack_iar_zf\\Components\\osal\\include\\OSAL.h"


/*********************************************************************
 * FUNCTIONS
 */

/*** Message Management ***/

  /*
   * Task Message Allocation
   */
  extern uint8 * osal_msg_allocate(uint16 len );

  /*
   * Task Message Deallocation
   */
  extern uint8 osal_msg_deallocate( uint8 *msg_ptr );

  /*
   * Send a Task Message
   */
  extern uint8 osal_msg_send( uint8 destination_task, uint8 *msg_ptr );

  /*
   * Push a Task Message to head of queue
   */
  extern uint8 osal_msg_push_front( uint8 destination_task, uint8 *msg_ptr );

  /*
   * Receive a Task Message
   */
  extern uint8 *osal_msg_receive( uint8 task_id );

  /*
   * Find in place a matching Task Message / Event.
   */
  extern osal_event_hdr_t *osal_msg_find(uint8 task_id, uint8 event);

  /*
   * Count the number of queued OSAL messages matching Task ID / Event.
   */
  extern uint8 osal_msg_count(uint8 task_id, uint8 event);

  /*
   * Enqueue a Task Message
   */
  extern void osal_msg_enqueue( osal_msg_q_t *q_ptr, void *msg_ptr );

  /*
   * Enqueue a Task Message Up to Max
   */
  extern uint8 osal_msg_enqueue_max( osal_msg_q_t *q_ptr, void *msg_ptr, uint8 max );

  /*
   * Dequeue a Task Message
   */
  extern void *osal_msg_dequeue( osal_msg_q_t *q_ptr );

  /*
   * Push a Task Message to head of queue
   */
  extern void osal_msg_push( osal_msg_q_t *q_ptr, void *msg_ptr );

  /*
   * Extract and remove a Task Message from queue
   */
  extern void osal_msg_extract( osal_msg_q_t *q_ptr, void *msg_ptr, void *prev_ptr );






/*** Task Synchronization  ***/

  /*
   * Set a Task Event
   */
  extern uint8 osal_set_event( uint8 task_id, uint16 event_flag );


  /*
   * Clear a Task Event
   */
  extern uint8 osal_clear_event( uint8 task_id, uint16 event_flag );


/*** Interrupt Management  ***/

  /*
   * Register Interrupt Service Routine (ISR)
   */
  extern uint8 osal_isr_register( uint8 interrupt_id, void (*isr_ptr)( uint8* ) );

  /*
   * Enable Interrupt
   */
  extern uint8 osal_int_enable( uint8 interrupt_id );

  /*
   * Disable Interrupt
   */
  extern uint8 osal_int_disable( uint8 interrupt_id );


/*** Task Management  ***/

#line 259 "F:\\Workspace\\zstack_iar_zf\\Components\\osal\\include\\OSAL.h"

  /*
   * Initialize the Task System
   */
  extern uint8 osal_init_system( void );

  /*
   * System Processing Loop
   */



  extern void osal_start_system( void );


  /*
   * One Pass Throu the OSAL Processing Loop
   */
  extern void osal_run_system( void );

  /*
   * Get the active task ID
   */
  extern uint8 osal_self( void );


/*** Helper Functions ***/

  /*
   * String Length
   */
  extern int osal_strlen( char *pString );

  /*
   * Memory copy
   */
  extern void *osal_memcpy( void*, const void  *, unsigned int );

  /*
   * Memory Duplicate - allocates and copies
   */
  extern void *osal_memdup( const void  *src, unsigned int len );

  /*
   * Reverse Memory copy
   */
  extern void *osal_revmemcpy( void*, const void  *, unsigned int );

  /*
   * Memory compare
   */
  extern uint8 osal_memcmp( const void  *src1, const void  *src2, unsigned int len );

  /*
   * Memory set
   */
  extern void *osal_memset( void *dest, uint8 value, int len );

  /*
   * Build a uint16 out of 2 bytes (0 then 1).
   */
  extern uint16 osal_build_uint16( uint8 *swapped );

  /*
   * Build a uint32 out of sequential bytes.
   */
  extern uint32 osal_build_uint32( uint8 *swapped, uint8 len );

  /*
   * Convert long to ascii string
   */

    extern uint8 *_ltoa( uint32 l, uint8 * buf, uint8 radix );


  /*
   * Random number generator
   */
  extern uint16 osal_rand( void );

  /*
   * Buffer an uint32 value - LSB first.
   */
  extern uint8* osal_buffer_uint32( uint8 *buf, uint32 val );

  /*
   * Buffer an uint24 value - LSB first
   */
  extern uint8* osal_buffer_uint24( uint8 *buf, uint24 val );

  /*
   * Is all of the array elements set to a value?
   */
  extern uint8 osal_isbufset( uint8 *buf, uint8 val, uint8 len );

/*********************************************************************
*********************************************************************/





#line 53 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\nwk\\AssocList.h"

/*********************************************************************
 * MACROS
 */

/*********************************************************************
 * CONSTANTS
 */






// Bitmap of associated devices status fields









// Node Relations
#line 86 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\nwk\\AssocList.h"

// Child Table age out values



/*********************************************************************
 * TYPEDEFS
 */

typedef struct
{
  uint8 endDevCfg;
  uint32 deviceTimeout;
} aging_end_device_t;

typedef struct
{
  uint16 shortAddr;                 // Short address of associated device
  uint16 addrIdx;                   // Index from the address manager
  byte nodeRelation;
  byte devStatus;                   // bitmap of various status values
  byte assocCnt;
  byte age;
  linkInfo_t linkInfo;
  aging_end_device_t endDev;
  uint32 timeoutCounter;
  _Bool keepaliveRcv;
} associated_devices_t;

typedef struct
{
  uint16 numRecs;
} nvDeviceListHdr_t;

/*********************************************************************
 * GLOBAL VARIABLES
 */
//extern byte _numAssocDev;
extern associated_devices_t AssociatedDevList[];

/*********************************************************************
 * FUNCTIONS
 */

/*
 * Variable initialization
 */
extern void AssocInit( void );

/*
 * Create a new or update a previous association.
 */
extern associated_devices_t *AssocAddNew( uint16 shortAddr, byte *extAddr,
                                                            byte nodeRelation );

/*
 * Count number of devices.
 */
extern uint16 AssocCount( byte startRelation, byte endRelation );

/*
 * Check if the device is a child.
 */
extern byte AssocIsChild( uint16 shortAddr );

/*
 * Check if the device is a reduced funtion child
 */
byte AssocIsRFChild( uint16 shortAddr );

/*
 * Check if the device is my parent.
 */
extern byte AssocIsParent( uint16 shortAddr );

/*
 * Search the Device list using shortAddr.
 */
extern associated_devices_t *AssocGetWithShort( uint16 shortAddr );

/*
 * Search the Device list using extended Address.
 */
extern associated_devices_t *AssocGetWithExt( byte *extAddr );

/*
 * Remove a device from the list. Uses the extended address.
 */
extern byte AssocRemove( byte *extAddr );

/*
 * Returns the next inactive child node
 */
extern uint16 AssocGetNextInactiveNode( uint16 shortAddr );

/*
 * Returns the next child node
 */
extern uint16 AssocGetNextChildNode( uint16 shortAddr );

/*
 * Remove all devices from the list and reset it
 */
extern void AssocReset( void );

/*
 * AssocMakeList - Make a list of associate devices
 *  NOTE:  this function returns a dynamically allocated buffer
 *         that MUST be deallocated (osal_mem_free).
 */
extern uint16 *AssocMakeList( byte *pCount );

/*
 * Gets next device that matches the status parameter
 */
extern associated_devices_t *AssocMatchDeviceStatus( uint8 status );

/*
 * Initialize the Assoc Device List NV Item
 */
extern byte AssocInitNV( void );

/*
 * Set Assoc Device list NV Item to defaults
 */
extern void AssocSetDefaultNV( void );

/*
 * Restore the device list (assoc list) from NV
 */
extern uint8 AssocRestoreFromNV( void );

/*
 * Save the device list (assoc list) to NV
 */
extern void AssocWriteNV( void );

/*
 * Find Nth active device in list
 */
extern associated_devices_t *AssocFindDevice( uint16 number );

extern uint8 AssocChangeNwkAddr( uint16 nwkAddr, uint8 *ieeeAddr );

extern void AssocCheckDupNeighbors( void );

extern void AssocChildAging( void );

extern uint8 AssocChildTableUpdateTimeout( uint16 nwkAddr );

extern void AssocChildTableManagement( osal_event_hdr_t *inMsg );

extern uint8 *AssocMakeListOfRfdChild( uint8 *pCount );

/*********************************************************************
*********************************************************************/







#line 52 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\nwk\\NLMEDE.h"


/*********************************************************************
 * MACROS
 */

/*********************************************************************
 * CONSTANTS
 */

// Tx Options (bitmap values)



// Route Discovery Options


                                  // intermediate router) will issue  a route
                                  // disc request.


// Beacon Order Values
#line 90 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\nwk\\NLMEDE.h"





/* Definition of scan application */




// CapabilityFlags Bitmap values
#line 108 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\nwk\\NLMEDE.h"

// ***********************   BROADCAST SUPPORT  **********************************
// Broadcast address definitions

enum  bcast_addr_e {
  NWK_BROADCAST_SHORTADDR_RESRVD_F8  = 0xFFF8,
  NWK_BROADCAST_SHORTADDR_RESRVD_F9,
  NWK_BROADCAST_SHORTADDR_RESRVD_FA,
  NWK_BROADCAST_SHORTADDR_RESRVD_FB,
  NWK_BROADCAST_SHORTADDR_DEVZCZR,            // 0xFFFC: Routers and Coordinators
  NWK_BROADCAST_SHORTADDR_DEVRXON,            // 0xFFFD: Everyone with RxOnWhenIdle == TRUE
                                              // 0xFFFE: Reserved (legacy: used for 'invalid address')
  NWK_BROADCAST_SHORTADDR_DEVALL     = 0xFFFF
};
typedef enum bcast_addr_e bcast_addr_t;


// Broadcast filter support
#line 136 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\nwk\\NLMEDE.h"
enum addr_filter_e  {
  ADDR_NOT_BCAST,     // not a broadcast address
  ADDR_BCAST_NOT_ME,  // broadcast address but not for me based on capabilities
  ADDR_BCAST_FOR_ME   // broadcast for me based on capabilities
};
typedef enum addr_filter_e addr_filter_t;

// Join indication type - MAC associate or rejoin







// ***********************   END BROADCAST SUPPORT  **********************************

// NV Enables - for use when saving NV [NLME_UpdateNV()]





/*********************************************************************
 * TYPEDEFS
 */
typedef enum
{
  nwkSequenceNum      = 0x81,
  nwkPassiveAckTimeout,
  nwkMaxBroadcastRetries,
  nwkMaxChildren,
  nwkMaxDepth,
  nwkMaxRouters,
  nwkNeighborTable,
  nwkBroadcastDeliveryTime,
  nwkReportConstantCost,
  nwkRouteDiscRetries,    // 0x8a
  nwkRoutingTable,
  nwkSecureAllFrames,
  nwkSecurityLevel,
  nwkSymLink,
  nwkCapabilityInfo,      // 0x8f

  // next 5 attributes are only needed for alternate addressing...
  //nwkUseTreeAddrAlloc,             // boolean
  //nwkUseTreeRouting,               // boolean
  //nwkNextAddress,                  // 16 bit
  //nwkAvailableAddresses,           // 16 bit
  //nwkAddressIncrement,             // 16 bit

  nwkTransactionPersistenceTime = 0x95,   // 16 bit

  //nwkShortAddress,                      // 16 bit
  //nwkStackProfile,
  nwkProtocolVersion = 0x98,
  //nwkAllowAddressReuse,                 // Boolean
  //nwkGroupIDTable,

  // non-standard items
  nwkRouteDiscoveryTime = 0x9B,
  nwkNumNeighborTableEntries,
  nwkNumRoutingTableEntries,
  nwkNwkState,
  nwkNwkPollTimeOut = 0xD8,
  nwkMAX_NIB_ITEMS            // Must be the last entry
}ZNwkAttributes_t;

typedef struct
{
  uint16 panId;
  byte logicalChannel;
  byte routerCapacity;
  byte deviceCapacity;
  byte version;
  byte stackProfile;
  uint16 chosenRouter;
  uint8 chosenRouterLinkQuality;
  uint8 chosenRouterDepth;
  uint8 extendedPANID[8];
  byte updateId;
  void *nextDesc;
} networkDesc_t;

// Src route subframe format
typedef struct
{
  uint8   relayCnt;
  uint8   relayIdx;
  uint16* relayList;
} NLDE_SrcFrameFormat_t;

typedef struct
{
  uint8  bufLength;
  uint8  hdrLen;
  uint8  frameType;
  uint8  protocolVersion;
  uint8  discoverRoute;
  uint8  multicast;
  uint8  secure;
  uint8  dstExtAddrSet;
  uint8  srcExtAddrSet;
  uint16 dstAddr;
  uint16 srcAddr;
  uint16 macDstAddr;
  uint16 transID;     // Only used in local messaging
  uint8  radius;
  uint8  broadcastId;
  uint8* dstExtAddr;
  uint8* srcExtAddr;
  uint8  nsduLength;
  uint8  srcRouteSet;    //If this flag is set, srcfd shall present
  NLDE_SrcFrameFormat_t srcfd;          //Source route frame data
  uint8* nsdu;
  uint16 macSrcAddr;
  uint16  txOptions;
  uint8   apsRetries;
  uint8   endDevInitiator;
  uint8   nsduHandle;
} NLDE_FrameFormat_t;

typedef struct
{
  uint8     LinkQuality;      /* The link quality of the received data frame */
  uint8     correlation;      /* The raw correlation value of the received data frame */
  int8      rssi;             /* The received RF power in units dBm */
} NLDE_Signal_t;



typedef struct
{
  uint8  frameType;
  uint8  hdrLen;
  uint16 dstAddr;
  uint16 srcAddr;
  uint8  srcRouteSet;   // If this flag is set, srcfd shall present
  NLDE_SrcFrameFormat_t srcfd;         // Source route frame data
  uint8* nsdu;
  uint8  nsduLen;
  uint8  nsduHandle;
  uint16 nsduHandleOptions;
  uint8  secure;
  uint8  discoverRoute;
  uint8  radius;
  uint8  seqNum;
  uint8  multicast;
  uint8  dstExtAddrSet;
  uint8  srcExtAddrSet;
  uint8* dstExtAddr;
  uint8* srcExtAddr;
  uint16 transID;     // Only used for local messaging
  uint16 txOptions;
  uint8  apsRetries;
  void*  fd;
  uint8  endDevInitiator;
} NLDE_FrameData_t;

typedef struct
{
//ZMacDataReq_t    mfd;
  NLDE_FrameData_t nfd;
} NLDE_DataReq_t;

typedef struct
{
  uint8 overhead;
  uint8 nsduLen;
  uint8 secure;
} NLDE_DataReqAlloc_t;

typedef struct
{
  uint32 channels;
  uint8  duration;
  uint8  scanType;
  uint8  scanApp;
} NLME_ScanFields_t;

typedef struct
{
  nwkDB_t*  db;
  ZStatus_t status;
  uint8     retries;
} NLDE_DataCnf_t;

typedef struct
{
  uint8* extAddr;
  uint8  removeChildren;
  uint8  rejoin;
  uint8  silent;
} NLME_LeaveReq_t;

typedef struct
{
  uint8 removeChildren;
  uint8 rejoin;
} NLME_LeaveRsp_t;

typedef struct
{
  uint16 dstAddr;
  uint8  extAddr[8];
  uint8  removeChildren;
  uint8  rejoin;
  uint8  status;
} NLME_LeaveCnf_t;

typedef struct
{
  uint16 srcAddr;
  uint8  extAddr[8];
  uint8  request;
  uint8  removeChildren;
  uint8  rejoin;
} NLME_LeaveInd_t;

typedef struct
{
  uint16 sourceAddr;
  uint16 panID;
  uint8  logicalChannel;
  uint8	 permitJoining;
  uint8	 routerCapacity;
  uint8	 deviceCapacity;
  uint8  protocolVersion;
  uint8  stackProfile ;
  uint8	 LQI ;
  uint8  depth ;
  uint8  updateID;
  uint8  extendedPanID[8];
} NLME_beaconInd_t;
/*********************************************************************
 * GLOBAL VARIABLES
 */
extern byte NLME_PermitJoining;
extern byte NLME_AssocPermission;
extern uint16 savedResponseRate;     // Backed response rate for rejoin request
extern uint16 savedQueuedPollRate;   // Backed queued poll rate

// network discovery scan fields
extern NLME_ScanFields_t* NLME_ScanFields;

/*********************************************************************
 * NWK Data Service
 *   NLDE-DATA
 */

/*
 * This function requests the transfer of data using the NWK layer
 * data service.
 *
 * @MT SPI_CMD_NLDE_DATA_REQ
 *
 */
extern ZStatus_t NLDE_DataReq( NLDE_DataReq_t* req );

/*
 * This function allocates a request buffer for use with the NWK layer
 * data service.
 *
 */
extern NLDE_DataReq_t* NLDE_DataReqAlloc( NLDE_DataReqAlloc_t* dra );

/*
 * This function reports the results of a request to transfer a data
 * PDU (NSDU) from a local APS sub-layer entity to a single peer APS
 * sub-layer entity.
 *
 * @MT SPI_CB_NLDE_DATA_CNF
 *
 */
extern void NLDE_DataCnf( NLDE_DataCnf_t* cnf );

/*
 * This function indicates the transfer of a data PDU (NSDU) from the
 * NWK layer to the local APS sub-layer entity.
 *
 * @MT SPI_CB_NLDE_DATA_IND
 */
extern void NLDE_DataIndication( NLDE_FrameFormat_t *ff,  NLDE_Signal_t *sig, uint32 timestamp );

/*********************************************************************
 * NWK Management Service
 *   NLME-NETWORK-FORMATION
 *   NLME-NETWORK-DISCOVERY
 *   NLME-PERMIT-JOINING
 *   NLME-JOIN
 *   NLME-DIRECT-JOIN
 *   NLME-ORPHAN-JOIN
 *   NLME-START-ROUTER
 *   NLME-SYNC
 *   NLME-LEAVE
 *   NLME-RESET
 *   NLME-GET
 *   NLME-SET
 */

/*
 * This function allows the next higher layer to request that the device
 * form a new network and become the ZigBee Coordinator for that network.
 *
 * @MT SPI_CMD_NLME_INIT_COORD_REQ
 * (uint16 PanId,
 *  uint32 ScanChannels,
 *  byte BeaconOrder,
 *  byte ScanDuration,
 *  byte SuperFrameOrder,
 *  byte BatteryLifeExtension,
 *  bool DistributedNetwork,
 *  int16 DistributedNetworkAddress)
 *
 */
extern ZStatus_t NLME_NetworkFormationRequest( uint16 PanId,  uint8* ExtendedPANID, uint32 ScanChannels,
                                               byte ScanDuration, byte BeaconOrder,
                                               byte SuperframeOrder, byte BatteryLifeExtension, _Bool DistributedNetwork, 
                                               uint16 DistributedNetworkAddress );

/*
 * This function reports the results of the request to form a new
 * network.
 *
 * @MT SPI_CB_NLME_INITCOORD_CNF
 *
 */
extern void NLME_NetworkFormationConfirm( ZStatus_t Status );

/* This function requests the NWK layer to discover neighboring routers
 *
 * @MT SPI_CMD_NLME_NWK_DISC_REQ
 *
 */
extern ZStatus_t NLME_NetworkDiscoveryRequest( uint32 ScanChannels,
                                               uint8  scanDuration);

/* This function allows the NWK layer to discover neighboring routers
 * without affecting the current nwk state
 */
extern ZStatus_t NLME_NwkDiscReq2( NLME_ScanFields_t* fields );

/* This function cleans up the NWK layer after a call to
 * NLME_NwkDiscReq2
 */
extern void NLME_NwkDiscTerm( void );

/* This function returns network discovery confirmation
 *
 * @MT SPI_CB_NLME_NWK_DISC_CNF
 *
 */
extern void NLME_NetworkDiscoveryConfirm(uint8 status);

extern uint8 NLME_GetRemainingPermitJoiningDuration( void );

/*
 * This function defines how the next higher layer of a coordinator device
 * to permit devices to join its network for a fixed period.
 *
 * @MT SPI_CMD_NLME_PERMIT_JOINING_REQ
 *
 */
extern ZStatus_t NLME_PermitJoiningRequest( byte PermitDuration );

/*
 * This function handles the NWK_PERMITJOIN_EVT event.
 *
 */
extern void NLME_PermitJoiningEvent( void );

/*
 * This function allows the next higher layer to request the device to join
 * itself to a specific network.
 *
 * @MT SPI_CMD_NLME_JOIN_REQ
 *
 */
extern ZStatus_t NLME_JoinRequest( uint8 *extendedPANID, uint16 PanId,
                             uint8 channel, uint8 CapabilityFlags,
                             uint16 chosenParent, uint8 parentDepth );
/*
 * This function allows the next higher layer to request to directly join
 * another device to this device
 * The result is contained in the return value and there is no confirm primitive
 *
 * @MT SPI_CMD_NLME_DIRECT_JOIN_REQ
 *
 */
extern ZStatus_t NLME_DirectJoinRequest( byte *DevExtAddress, byte capInfo );

/*
 * This function allows the next higher layer to request to directly join
 * another device, specified by the short address, to this device
 * The result is contained in the return value and there is no confirm primitive
 */
extern ZStatus_t NLME_DirectJoinRequestWithAddr( byte *DevExtAddress, uint16 shortAddress, uint8 capInfo );

/*
 * This function allows the next higher layer to request the device
 * to search for its parent.
 *
 * @MT SPI_CMD_NLME_ORPHAN_JOIN_REQ
 *
 */
extern ZStatus_t NLME_OrphanJoinRequest( uint32 ScanChannels, byte ScanDuration );



/*
 * This function allows the next higher layer to set the nwk state to parent lost.
 */
extern void NLME_OrphanStateSet(void);



/*
 * This function allows the next higher layer to request the device
 * to rejoin the network.
 */
extern ZStatus_t NLME_ReJoinRequest( uint8 *ExtendedPANID, uint8 channel );

/*
 * This function allows the next higher layer to request the device
 * to rejoin the network "non-securely".
 */
extern ZStatus_t NLME_ReJoinRequestUnsecure( uint8 *ExtendedPANID, uint8 channel );

/*
 * This function allows the next higher layer to be notified of the
 * results of its request to join itself to a network.
 *
 * @MT SPI_CB_NLME_JOIN_CNF
 * (byte *DeviceAddress,
 *  uint16 PanId,
 *  byte Status)
 *
 */
extern void NLME_JoinConfirm( uint16 PanId, ZStatus_t Status );

/*
 * This function allows the next higher layer of a coordinator to be
 * notified of a remote join request.
 *
 * @MT SPI_CB_NLME_JOIN_IND
 *
 */
extern ZStatus_t NLME_JoinIndication( uint16 ShortAddress,
                                      uint8 *ExtendedAddress,
                                      uint8 CapabilityFlags,
                                      uint8 type );

/*
 * This function allows the next higher layer to request a device to function
 * as a router. NOTE: the BeaconOrder and SuperframeOrder parameters are not
 *  used in this version -- the values obtained during network formation or
 * joining are used instead, ensuring commonality with the ZDO COORDINATOR.
 *
 * @MT SPI_CMD_NLME_START_ROUTER_REQ
 *
 */
extern ZStatus_t NLME_StartRouterRequest( byte BeaconOrder,
                                          byte SuperframeOrder,
                                          byte BatteryLifeExtension  );

/*
 * This function reports the results of the request  to start
 * functioning as a router.
 *
 * @MT SPI_CB_NLME_START_ROUTER_CNF
 *
 */
extern void NLME_StartRouterConfirm( ZStatus_t Status );

/*
 * This function reports the beacon notification received due
 * to network discovery
 *
 */
extern void NLME_beaconNotifyInd(NLME_beaconInd_t *pBeacon);

/*
 * This function allows the next higher layer to request that itself
 * or another device leave the network.
 *
 * @MT SPI_CMD_NLME_LEAVE_REQ
 *
 */
extern ZStatus_t NLME_LeaveReq( NLME_LeaveReq_t* req );

/*
 * This function allows the next higher layer to be notified of the
 * results of its request for itself or another device to leave the
 * network.
 *
 * @MT SPI_CB_NLME_LEAVE_CNF
 *
 */
extern void NLME_LeaveCnf( NLME_LeaveCnf_t* cnf );

/*
 * This function allows the next higher layer of a device to be
 * notified of a remote leave request.
 *
 * @MT SPI_CB_NLME_LEAVE_IND
 *
 */
extern void NLME_LeaveInd( NLME_LeaveInd_t* ind );

/*
 * This function allows the next higher layer to respond to a leave
 * indication.
 */
extern ZStatus_t NLME_LeaveRsp( NLME_LeaveRsp_t* rsp );

/*
 * This function allows the next higher layer to request that the NWK layer
 * perform a reset operation.
 *
 * @MT SPI_CMD_NLME_RESET_REQ
 *
 */
extern ZStatus_t NLME_ResetRequest( void );

/*
 * This function allows the next higher layer to request
 * synchronization with its parent and extract data
 *
 * @MT SPI_CMD_NLME_SYNC_REQ
 */

extern ZStatus_t NLME_SyncRequest( byte Track );

/*
 * This function allows the next higher layer to be notified of the
 * loss of synchronization at the MAC sub-layer.
 *
 * @MT SPI_CB_NLME_SYNC_IND
 * (byte Status)
 *
 */
extern void NLME_SyncIndication( byte type, uint16 shortAddr );

/*
 * This function stub allows the next higher layer to be notified of
 * a permit joining timeout.
 */
extern void NLME_PermitJoiningTimeout( void );

/*
 * This function allows the next higher layer to be notified of a
 * Poll Confirm from the MAC sub-layer.
 *
 * @MT SPI_CB_NLME_POLL_CNF
 * (byte Status)
 *
 */
extern void NLME_PollConfirm( byte status );

/*
 * This function allows the next higher layer to read the value of
 * an attribute from the NIB.
 *
 * @MT SPI_CMD_NLME_GET_REQ
 *
 */
extern ZStatus_t NLME_GetRequest( ZNwkAttributes_t NIBAttribute, uint16 Index,
                                    void *Value );

/*
 * This function allows the next higher layer to write the value of an
 * attribute into the NIB.
 *
 * @MT SPI_CMD_NLME_SET_REQ
 *
 */
extern ZStatus_t NLME_SetRequest( ZNwkAttributes_t NIBAttribute,
                                  uint16 Index,
                                  void *Value );
/*
 * This function allows the higher layers to initiate route discovery
 * to a given destination address
 *
 * @MT SPI_CMD_NLME_ROUTE_DISC_REQ
 *
 */
extern ZStatus_t NLME_RouteDiscoveryRequest( uint16 DstAddress, byte options, uint8 radius );


/*
 * This function allow to indicate to higher layer the existence of
 * concentrator and its nwk address
 */
extern void NLME_ConcentratorIndication( uint16 nwkAddr, uint8 *extAddr, uint8 pktCost );

/*
 * This function allows the next higher layer to request an energy scan
 * to evaluate channels in the local area.
 */
extern ZStatus_t NLME_EDScanRequest( uint32 ScanChannels, uint8 scanDuration);

/*
 * This function returns list of energy measurements.
 */
extern void NLME_EDScanConfirm( uint8 status, uint32 scannedChannels, uint8 *energyDetectList );

/*********************************************************************
 * NWK Helper Functions
 */

/*
 * This function will return a pointer to the device's IEEE 64 bit address
 *
 * This function resides in nwk_util.c.
 */
extern byte *NLME_GetExtAddr( void );

/*
 * This function will return this device's 16 bit short address
 *
 * This function resides in nwk_util.c.
 */
extern uint16 NLME_GetShortAddr( void );

/*
 * This function will return the MAC's Coordinator's short (16bit) address
 * which is this device's parent, not necessarily the Zigbee coordinator.
 *
 * This function resides in nwk_util.c.
 */
extern uint16 NLME_GetCoordShortAddr( void );

/*
 * This function will return the MAC's Coordinator's Extented (64bit) address
 * which is this device's parent, not necessarily the Zigbee coordinator.
 *
 * This function resides in nwk_util.c.
 */
extern void NLME_GetCoordExtAddr( byte * );

/*
 * Use this function to request a single MAC data request.
 */
extern ZMacStatus_t NwkPollReq( byte securityEnable );

/*
 * Use this function to set/change the Network Poll Rate. If the
 * newRate is set to 0, it will turn off the auto polling, 1 will do a
 * one time poll.
 */
extern void NLME_SetPollRate( uint32 newRate );

/*
 * Use this function to set/change the Network Queued Poll Rate.
 * This is used after receiving a data indication to poll immediately
 * for queued messages.
 */
extern void NLME_SetQueuedPollRate( uint16 newRate );

/*
 * Use this function to set/change the Network Queued Poll Rate.
 * This is used after receiving a data confirmation to poll immediately
 * for response messages.
 */
extern void NLME_SetResponseRate( uint16 newRate );

/*
 * Initialize the Nwk, Assoc device list, and binding NV Items
 *   returns SUCCESS if successful otherwise an error bitmask.
 */
extern byte NLME_InitNV( void );

/*
 * Set defaults for the Nwk, Assoc device list, and binding NV Items
 */
extern void NLME_SetDefaultNV( void );

/*
 * Restore network memory items from NV.
 */
extern byte NLME_RestoreFromNV( void );

/*
 * Write network items to NV.
 *        enables - bit mask of items to save:
 *                     NWK_NV_NIB_ENABLE
 *                     NWK_NV_DEVICELIST_ENABLE
 *                     NWK_NV_BINDING_ENABLE
 *                     NWK_NV_ADDRMGR_ENABLE
 */
void NLME_UpdateNV( byte enables );

/*
 * NLME_CheckNewAddrSet
 *
 * We have a new address pair (short and extended) - check our database.
 *     dontChange - Don't change our address just issue conflict (It was taken
 *                  out since the Spec was changed again. All devices will
 *                  change address upon any circumstances.
 *
 * Returns      ZSuccess if in data base and matches
 *              ZUnsupportedMode if not in database
 *              ZFailure if short address is in database,
 *                   but extended address doesn't match database
 *
 * If ZFailure is returned, the stack already sent out an address conflict
 * route error - already called NLME_ReportAddressConflict().
 */
extern ZStatus_t NLME_CheckNewAddrSet( uint16 shortAddr, uint8 *extAddr );

/*
 * Issues a Router Error with Address conflict and handles the
 * conflict locally for itself and children (RFDs).
 */
extern void NLME_ReportAddressConflict( uint16 shortAddr, uint8 forceSpecialMode );


extern void NLME_CoordinatorInit( void );
extern void NLME_DeviceJoiningInit( void );

extern void (*pnwk_ScanPANChanSelect)( ZMacScanCnf_t *param );
extern void (*pnwk_ScanPANChanVerify)( ZMacScanCnf_t *param );
extern void (*pNLME_NetworkFormationConfirm)( ZStatus_t Status );

extern ZStatus_t NLME_ReadNwkKeyInfo(uint16 index, uint16 len, void *keyinfo, uint16 NvId);

/****************************************************************************
****************************************************************************/







#line 55 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\nwk\\nwk.h"
#line 1 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\sec\\ssp.h"
/**************************************************************************************************
  Filename:       ssp.h
  Revised:        $Date: 2014-11-18 02:32:26 -0800 (Tue, 18 Nov 2014) $
  Revision:       $Revision: 41160 $

  Description:    Security Service Provider (SSP) interface


  Copyright 2004-2014 Texas Instruments Incorporated. All rights reserved.

  IMPORTANT: Your use of this Software is limited to those specific rights
  granted under the terms of a software license agreement between the user
  who downloaded the software, his/her employer (which must be your employer)
  and Texas Instruments Incorporated (the "License").  You may not use this
  Software unless you agree to abide by the terms of the License. The License
  limits your use, and you acknowledge, that the Software may not be modified,
  copied or distributed unless embedded on a Texas Instruments microcontroller
  or used solely and exclusively in conjunction with a Texas Instruments radio
  frequency transceiver, which is integrated into your product.  Other than for
  the foregoing purpose, you may not use, reproduce, copy, prepare derivative
  works of, modify, distribute, perform, display or sell this Software and/or
  its documentation for any purpose.

  YOU FURTHER ACKNOWLEDGE AND AGREE THAT THE SOFTWARE AND DOCUMENTATION ARE
  PROVIDED "AS IS" WITHOUT WARRANTY OF ANY KIND, EITHER EXPRESS OR IMPLIED,
  INCLUDING WITHOUT LIMITATION, ANY WARRANTY OF MERCHANTABILITY, TITLE,
  NON-INFRINGEMENT AND FITNESS FOR A PARTICULAR PURPOSE. IN NO EVENT SHALL
  TEXAS INSTRUMENTS OR ITS LICENSORS BE LIABLE OR OBLIGATED UNDER CONTRACT,
  NEGLIGENCE, STRICT LIABILITY, CONTRIBUTION, BREACH OF WARRANTY, OR OTHER
  LEGAL EQUITABLE THEORY ANY DIRECT OR INDIRECT DAMAGES OR EXPENSES
  INCLUDING BUT NOT LIMITED TO ANY INCIDENTAL, SPECIAL, INDIRECT, PUNITIVE
  OR CONSEQUENTIAL DAMAGES, LOST PROFITS OR LOST DATA, COST OF PROCUREMENT
  OF SUBSTITUTE GOODS, TECHNOLOGY, SERVICES, OR ANY CLAIMS BY THIRD PARTIES
  (INCLUDING BUT NOT LIMITED TO ANY DEFENSE THEREOF), OR OTHER SIMILAR COSTS.

  Should you have any questions regarding your right to use this Software,
  contact Texas Instruments Incorporated at www.TI.com.
**************************************************************************************************/









/*********************************************************************
 * INCLUDES
 */


/*********************************************************************
 * MACROS
 */

/*********************************************************************
 * CONSTANTS
 */




// Auxiliary header field lengths

//Threshold after which the frame counter will be reset if a valid APSME-SWITCH-KEY is processed.

  






// Security Key Indentifiers





// Security Levels











// Key types

























// SSP_MacTagData_t::type



// Error value used when security key NV ID is not available


 
/*********************************************************************
 * TYPEDEFS
 */

typedef struct
{
  uint8 keySeqNum;
  uint8 key[16];
} nwkKeyDesc;

typedef struct
{
  nwkKeyDesc  active;
  uint32      frameCounter;
} nwkActiveKeyItems;

typedef struct
{
  uint8 hdrLen;
  uint8 auxLen;
  uint8 msgLen;
  uint8 secLevel;
  uint8 keyId;
  uint32 frameCtr;
  uint8 *key;
} ssp_ctx;

typedef struct
{
  uint8* initExtAddr;
  uint8* rspExtAddr;
  uint8* key;
  uint8* qeu;
  uint8* qev;
  uint8* text1;
  uint8* text2;
  uint8* tag1;
  uint8* tag2;
  uint8* linkKey;
  uint8  type;
} SSP_MacTagData_t;

typedef struct
{
  uint8  dir;
  uint8  secLevel;
  uint8  hdrLen;
  uint8  sduLen;   //service data unit length
  uint8* pdu;      //protocol data unit
  uint8  extAddr[8];
  uint8  keyID;
  uint16 keyNvId; // NV ID of key: NWK, TCLK or APS
  uint8  keySeqNum;
  uint32 frmCntr;
  uint8  auxLen;
  uint8  micLen;
  uint8  dstExtAddr[8];
  _Bool   distributedKeyTry;  //Attempting to validate if TransportKey uses distributed key
  _Bool   defaultKeyTry;      //Attempting to validate if TransportKey uses default key when install code is in use
  uint8  seedShift;
} SSP_Info_t;

/*********************************************************************
 * GLOBAL VARIABLES
 */
extern uint32 nwkFrameCounter;
extern uint32 distributedFrameCounter;
extern uint16 nwkFrameCounterChanges;

/*********************************************************************
 * FUNCTIONS
 */

/*
 * SSP Initialization
 */
extern void SSP_Init( void );

/*
 * Parse Auxillary Header
 */
extern void SSP_ParseAuxHdr( SSP_Info_t* si );

/*
 * Process Security Information
 */
extern ZStatus_t SSP_Process( SSP_Info_t* si );

/*
 * Process MAC TAG Data - Generate Tags
 */
extern ZStatus_t SSP_GetMacTags( SSP_MacTagData_t* data );

/*
 * Returns Random Bits
 */
extern void SSP_GetTrueRand( uint8 len, uint8 *rand );

/*
 * Returns 8*len random bits using AES based mechanism
 * ( currently less than 128 bits )
 */
extern ZStatus_t SSP_GetTrueRandAES( uint8 len, uint8 *rand );

/*
 * Store the 16 byte random seed in NV
 */
extern void SSP_StoreRandomSeedNV( uint8 *pSeed );

/*
 * Read the network active key information
 */
extern void SSP_ReadNwkActiveKey( nwkActiveKeyItems *items );

/*
 * Get the index for the selected network key in NV
 */
extern uint16 SSP_GetNwkKey( uint8 seqNum );

/*
 * Secure/Unsecure a network PDU
 */
extern ZStatus_t SSP_NwkSecurity(uint8 ed_flag, uint8 *msg, uint8 hdrLen, uint8 nsduLen);

/*
 * Set the alternate network key
 */
extern void SSP_UpdateNwkKey( uint8 *key, uint8 keySeqNum );

/*
 * Make the alternate network key as active
 */
extern void SSP_SwitchNwkKey( uint8 seqNum );

extern void SSP_BuildNonce( uint8 *addr, uint32 frameCntr, uint8 secCtrl, uint8 *nonce );

extern uint8 SSP_GetMicLen( uint8 securityLevel );

/*
 * Duplicate osal_memcpy functionality, but reverse copy
 */
extern uint8* SSP_MemCpyReverse( uint8* dst, uint8* src, unsigned int len );

/*********************************************************************
*********************************************************************/




#line 56 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\nwk\\nwk.h"

/*********************************************************************
 * MACROS
 */

/*********************************************************************
 * CONSTANTS
 */

//NWK event identifiers
#line 73 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\nwk\\nwk.h"

#line 87 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\nwk\\nwk.h"
// Event 0x8000 is Reserved for SYS_EVENT_MSG

//NWK PACKET: FIELD IDENTIFIERS
#line 96 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\nwk\\nwk.h"

// This value needs to be set or read from somewhere


// Max length of packet that can be sent to the MAC














// TxOptions for a data request - Indirect data and ACK required


// TxOptions for a data request - Direct data and ACK required
//#define NWK_TXOPTIONS_COORD       (NWK_TXOPTIONS_ACK)

//Assume value until defined By SuperApp or design spec









//#define DEF_BEACON_ORDER         10   // 15 seconds
//#define DEF_BEACON_ORDER         9    // 7.5 seconds
//#define DEF_BEACON_ORDER         8    // 3.75 seconds
//#define DEF_BEACON_ORDER         6    // 1 second
//#define DEF_BEACON_ORDER         1    // 30 millisecond

//#define DEF_SUPERFRAMEORDER      2
#line 144 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\nwk\\nwk.h"











// Link cost constants









// Link counter constants



//NWK Callback subscription IDs
#line 183 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\nwk\\nwk.h"









// The value of this event should larger than the maximum value of the MAC events


// Status of child device


// Router parent capabilities information bitmask
// Bits   Value    Description
//   0    0x01     MAC Data Poll Keepalive Supported


   

   
/*********************************************************************
 * TYPEDEFS
 */
typedef enum
{
  NWK_INIT,
  NWK_JOINING_ORPHAN,
  NWK_DISC,
  NWK_JOINING,
  NWK_ENDDEVICE,
  PAN_CHNL_SELECTION,
  PAN_CHNL_VERIFY,
  PAN_STARTING,
  NWK_ROUTER,
  NWK_REJOINING
} nwk_states_t;

// MAC Command Buffer types
typedef enum
{
  MACCMDBUF_NONE,
  MACCMDBUF_ASSOC_REQ,
  MACCMDBUF_DISASSOC_REQ
} nwkMacCmds_t;

typedef struct
{
  byte  SequenceNum;
  byte  PassiveAckTimeout;
  byte  MaxBroadcastRetries;
  byte  MaxChildren;
  byte  MaxDepth;
  byte  MaxRouters;

  byte  dummyNeighborTable;     // to make everything a byte!!

  byte  BroadcastDeliveryTime;
  byte  ReportConstantCost;
  byte  RouteDiscRetries;

  byte  dummyRoutingTable;      // to make everything a byte!!

  byte  SecureAllFrames;
  byte  SecurityLevel;



  byte  SymLink;
  byte  CapabilityFlags;

  uint16 TransactionPersistenceTime;

  byte   nwkProtocolVersion;

  // non-standard attributes
  byte  RouteDiscoveryTime;
  byte  RouteExpiryTime;        // set to 0 to turn off expiration of routes

  // non-settable
  uint16  nwkDevAddress;
  byte    nwkLogicalChannel;
  uint16  nwkCoordAddress;
  byte    nwkCoordExtAddress[8];
  uint16  nwkPanId;

  // Other global items - non-settable
  nwk_states_t  nwkState;
  uint32        channelList;
  byte          beaconOrder;
  byte          superFrameOrder;
  byte          scanDuration;
  byte          battLifeExt;
  uint32        allocatedRouterAddresses;
  uint32        allocatedEndDeviceAddresses;
  byte          nodeDepth;

  // Version 1.1 - extended PAN ID
  uint8         extendedPANID[8];

  // Network key flag
  uint8      nwkKeyLoaded;
  // Key information - Moved out of the NIB structure after ZStack 2.3.0
  // If these elements are going to be reused make sure to consider the size
  // of the structures and padding specific to the target where the stack is
  // going to be running.
  nwkKeyDesc spare1;    // Not used
  nwkKeyDesc spare2;    // Not used

  // Zigbee Pro extensions
  uint8      spare3;                // nwkAddrAlloc deprecated - not used anymore
  uint8      spare4;                // nwkUniqueAddr deprecated - not used anymore
  uint8      nwkLinkStatusPeriod;   // The time in seconds betwee link status
                                    // command frames
  uint8      nwkRouterAgeLimit;     // The number of missed link status
                                    // command frames before resetting the
                                    // link cost to zero
  uint8      nwkUseMultiCast;
  // ZigBee Pro extentions: MTO routing
  uint8      nwkIsConcentrator;             // If set, then the device is concentrator
  uint8      nwkConcentratorDiscoveryTime;  // Time period between two consecutive MTO route discovery
  uint8      nwkConcentratorRadius;         // Broadcast radius of the MTO route discovery





  uint8      nwkAllFresh;


  uint16     nwkManagerAddr;        // Network Manager Address
  uint16     nwkTotalTransmissions;
  uint8      nwkUpdateId;
} nwkIB_t;

// Scanned PAN IDs to be used for Network Report command
typedef struct
{
  uint16 panId;
  void   *next;
} nwkPanId_t;

/*********************************************************************
 * GLOBAL VARIABLES
 */
extern nwkIB_t _NIB;
extern byte NWK_TaskID;
extern networkDesc_t *NwkDescList;
extern byte nwkExpectingMsgs;
extern byte nwk_beaconPayload[(7 + 8)];
extern byte nwk_beaconPayloadSize;

extern uint8 nwkSendMTOReq;

/*********************************************************************
 * FUNCTIONS
 */

 /*
 * NWK Task Initialization
 */
extern void nwk_init( byte task_id );

 /*
 * Calls mac_data_req then handles the buffering
 */
extern ZStatus_t nwk_data_req_send( nwkDB_t* db );

 /*
 * NWK Event Loop
 */
extern UINT16 nwk_event_loop( byte task_id, UINT16 events );

 /*
 * Process incoming command packet
 */
//extern void CommandPktProcessing( NLDE_FrameFormat_t *ff );

/*
* Start a coordinator
*/
extern ZStatus_t nwk_start_coord( void );

/*
 * Free any network discovery data
 */
extern void nwk_desc_list_free( void );

/*
 * This function sets to null the discovery nwk list
 */
extern void nwk_desc_list_release(void);

extern networkDesc_t *nwk_getNetworkDesc( uint8 *ExtendedPANID, uint16 PanId, byte Channel );
extern networkDesc_t *nwk_getNwkDescList( void );

extern void nwk_BeaconFromNative(byte* buff, byte size, beaconPayload_t* beacon);
extern void nwk_BeaconToNative(beaconPayload_t* beacon, byte* buff, byte size);

/*
 * Set NWK task's state
 */
extern void nwk_setStateIdle( uint8 idle );

/*
 * Returns TRUE if NWK state is idle, FALSE otherwise.
 */
extern uint8 nwk_stateIdle( void );

/*********************************************************************
 * Functionality - not to be called directly.
 */
extern void nwk_ScanPANChanSelect( ZMacScanCnf_t *param );
extern void nwk_ScanPANChanVerify( ZMacScanCnf_t *param );

/*
 *  Special Send Leave Posts the message directly to MAC without buffering it
 */
extern ZStatus_t nwk_send_direct_leave_req( nwkDB_t* db );

/*********************************************************************
*********************************************************************/




#line 53 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\af\\AF.h"
#line 1 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\nwk\\APSMEDE.h"
/**************************************************************************************************
  Filename:       APSMEDE.h
  Revised:        $Date: 2015-06-02 15:55:43 -0700 (Tue, 02 Jun 2015) $
  Revision:       $Revision: 43961 $

  Description:    Primitives of the Application Support Sub Layer Data Entity (APSDE) and
                  Management Entity (APSME).


  Copyright 2004-2015 Texas Instruments Incorporated. All rights reserved.

  IMPORTANT: Your use of this Software is limited to those specific rights
  granted under the terms of a software license agreement between the user
  who downloaded the software, his/her employer (which must be your employer)
  and Texas Instruments Incorporated (the "License").  You may not use this
  Software unless you agree to abide by the terms of the License. The License
  limits your use, and you acknowledge, that the Software may not be modified,
  copied or distributed unless embedded on a Texas Instruments microcontroller
  or used solely and exclusively in conjunction with a Texas Instruments radio
  frequency transceiver, which is integrated into your product.  Other than for
  the foregoing purpose, you may not use, reproduce, copy, prepare derivative
  works of, modify, distribute, perform, display or sell this Software and/or
  its documentation for any purpose.

  YOU FURTHER ACKNOWLEDGE AND AGREE THAT THE SOFTWARE AND DOCUMENTATION ARE
  PROVIDED "AS IS" WITHOUT WARRANTY OF ANY KIND, EITHER EXPRESS OR IMPLIED,
  INCLUDING WITHOUT LIMITATION, ANY WARRANTY OF MERCHANTABILITY, TITLE,
  NON-INFRINGEMENT AND FITNESS FOR A PARTICULAR PURPOSE. IN NO EVENT SHALL
  TEXAS INSTRUMENTS OR ITS LICENSORS BE LIABLE OR OBLIGATED UNDER CONTRACT,
  NEGLIGENCE, STRICT LIABILITY, CONTRIBUTION, BREACH OF WARRANTY, OR OTHER
  LEGAL EQUITABLE THEORY ANY DIRECT OR INDIRECT DAMAGES OR EXPENSES
  INCLUDING BUT NOT LIMITED TO ANY INCIDENTAL, SPECIAL, INDIRECT, PUNITIVE
  OR CONSEQUENTIAL DAMAGES, LOST PROFITS OR LOST DATA, COST OF PROCUREMENT
  OF SUBSTITUTE GOODS, TECHNOLOGY, SERVICES, OR ANY CLAIMS BY THIRD PARTIES
  (INCLUDING BUT NOT LIMITED TO ANY DEFENSE THEREOF), OR OTHER SIMILAR COSTS.

  Should you have any questions regarding your right to use this Software,
  contact Texas Instruments Incorporated at www.TI.com.
**************************************************************************************************/








/******************************************************************************
 * INCLUDES
 */
#line 1 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\nwk\\nwk_globals.h"
/**************************************************************************************************
  Filename:       nwk_globals.h
  Revised:        $Date: 2015-01-08 16:32:12 -0800 (Thu, 08 Jan 2015) $
  Revision:       $Revision: 41678 $

  Description:    User definable Network Parameters.


  Copyright 2004-2015 Texas Instruments Incorporated. All rights reserved.

  IMPORTANT: Your use of this Software is limited to those specific rights
  granted under the terms of a software license agreement between the user
  who downloaded the software, his/her employer (which must be your employer)
  and Texas Instruments Incorporated (the "License").  You may not use this
  Software unless you agree to abide by the terms of the License. The License
  limits your use, and you acknowledge, that the Software may not be modified,
  copied or distributed unless embedded on a Texas Instruments microcontroller
  or used solely and exclusively in conjunction with a Texas Instruments radio
  frequency transceiver, which is integrated into your product.  Other than for
  the foregoing purpose, you may not use, reproduce, copy, prepare derivative
  works of, modify, distribute, perform, display or sell this Software and/or
  its documentation for any purpose.

  YOU FURTHER ACKNOWLEDGE AND AGREE THAT THE SOFTWARE AND DOCUMENTATION ARE
  PROVIDED "AS IS" WITHOUT WARRANTY OF ANY KIND, EITHER EXPRESS OR IMPLIED,
  INCLUDING WITHOUT LIMITATION, ANY WARRANTY OF MERCHANTABILITY, TITLE,
  NON-INFRINGEMENT AND FITNESS FOR A PARTICULAR PURPOSE. IN NO EVENT SHALL
  TEXAS INSTRUMENTS OR ITS LICENSORS BE LIABLE OR OBLIGATED UNDER CONTRACT,
  NEGLIGENCE, STRICT LIABILITY, CONTRIBUTION, BREACH OF WARRANTY, OR OTHER
  LEGAL EQUITABLE THEORY ANY DIRECT OR INDIRECT DAMAGES OR EXPENSES
  INCLUDING BUT NOT LIMITED TO ANY INCIDENTAL, SPECIAL, INDIRECT, PUNITIVE
  OR CONSEQUENTIAL DAMAGES, LOST PROFITS OR LOST DATA, COST OF PROCUREMENT
  OF SUBSTITUTE GOODS, TECHNOLOGY, SERVICES, OR ANY CLAIMS BY THIRD PARTIES
  (INCLUDING BUT NOT LIMITED TO ANY DEFENSE THEREOF), OR OTHER SIMILAR COSTS.

  Should you have any questions regarding your right to use this Software,
  contact Texas Instruments Incorporated at www.TI.com.
**************************************************************************************************/








/*********************************************************************
 * INCLUDES
 */

#line 1 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\nwk\\BindingTable.h"
/**************************************************************************************************
  Filename:       BindingTable.h
  Revised:        $Date: 2014-07-16 11:03:22 -0700 (Wed, 16 Jul 2014) $
  Revision:       $Revision: 39430 $

  Description:    Device binding table.


  Copyright 2004-2013 Texas Instruments Incorporated. All rights reserved.

  IMPORTANT: Your use of this Software is limited to those specific rights
  granted under the terms of a software license agreement between the user
  who downloaded the software, his/her employer (which must be your employer)
  and Texas Instruments Incorporated (the "License").  You may not use this
  Software unless you agree to abide by the terms of the License. The License
  limits your use, and you acknowledge, that the Software may not be modified,
  copied or distributed unless embedded on a Texas Instruments microcontroller
  or used solely and exclusively in conjunction with a Texas Instruments radio
  frequency transceiver, which is integrated into your product.  Other than for
  the foregoing purpose, you may not use, reproduce, copy, prepare derivative
  works of, modify, distribute, perform, display or sell this Software and/or
  its documentation for any purpose.

  YOU FURTHER ACKNOWLEDGE AND AGREE THAT THE SOFTWARE AND DOCUMENTATION ARE
  PROVIDED "AS IS" WITHOUT WARRANTY OF ANY KIND, EITHER EXPRESS OR IMPLIED,
  INCLUDING WITHOUT LIMITATION, ANY WARRANTY OF MERCHANTABILITY, TITLE,
  NON-INFRINGEMENT AND FITNESS FOR A PARTICULAR PURPOSE. IN NO EVENT SHALL
  TEXAS INSTRUMENTS OR ITS LICENSORS BE LIABLE OR OBLIGATED UNDER CONTRACT,
  NEGLIGENCE, STRICT LIABILITY, CONTRIBUTION, BREACH OF WARRANTY, OR OTHER
  LEGAL EQUITABLE THEORY ANY DIRECT OR INDIRECT DAMAGES OR EXPENSES
  INCLUDING BUT NOT LIMITED TO ANY INCIDENTAL, SPECIAL, INDIRECT, PUNITIVE
  OR CONSEQUENTIAL DAMAGES, LOST PROFITS OR LOST DATA, COST OF PROCUREMENT
  OF SUBSTITUTE GOODS, TECHNOLOGY, SERVICES, OR ANY CLAIMS BY THIRD PARTIES
  (INCLUDING BUT NOT LIMITED TO ANY DEFENSE THEREOF), OR OTHER SIMILAR COSTS.

  Should you have any questions regarding your right to use this Software,
  contact Texas Instruments Incorporated at www.TI.com.
**************************************************************************************************/








/*********************************************************************
 * INCLUDES
 */






/*********************************************************************
 * MACROS
 */

/*********************************************************************
 * CONSTANTS
 */





/*********************************************************************
 * TYPEDEFS
 */

typedef struct
{
  uint16 numRecs;
} nvBindingHdr_t;

// Don't use sizeof( BindingEntry_t ) use gBIND_REC_SIZE when calculating
// the size of each binding table entry. gBIND_REC_SIZE is defined in nwk_global.c.
typedef struct
{
                        // No src address since the src is always the local device
  uint8 srcEP;
  uint8 dstGroupMode;   // Destination address type; 0 - Normal address index, 1 - Group address
  uint16 dstIdx;        // This field is used in both modes (group and non-group) to save NV and RAM space
                        // dstGroupMode = 0 - Address Manager index
                        // dstGroupMode = 1 - Group Address
  uint8 dstEP;
  uint8 numClusterIds;
  uint16 clusterIdList[4];
                      // Don't use MAX_BINDING_CLUSTERS_ID when
                      // using the clusterIdList field.  Use
                      // gMAX_BINDING_CLUSTER_IDS
} BindingEntry_t;

/*********************************************************************
 * GLOBAL VARIABLES
 */

// BindingTable is defined in nwk_globals.c and NWK_MAX_BINDING_ENTRIES
// is defined in f8wConfig.cfg. Don't use NWK_MAX_BINDING_ENTRIES as the
// number of records - use gNWK_MAX_BINDING_ENTRIES.
extern BindingEntry_t BindingTable[];

/*********************************************************************
 * FUNCTIONS
 */

/*
 * This function is used to initialise the binding table
 */
extern void InitBindingTable( void );

/*
 * Removes a binding table entry.
 */
extern byte bindRemoveEntry( BindingEntry_t *pBind );

/*
 * Is the clusterID in the clusterID list?
 */
extern byte bindIsClusterIDinList( BindingEntry_t *entry, uint16 clusterId );

/*
 * Removes a ClusterID from a list of ClusterIDs.
 */
extern byte bindRemoveClusterIdFromList( BindingEntry_t *entry, uint16 clusterId );

/*
 * Adds a ClusterID to a list of ClusterIDs.
 */
extern byte bindAddClusterIdToList( BindingEntry_t *entry, uint16 clusterId );

/*
 * Finds an existing src/epint to dst/epint bind record
 */
extern BindingEntry_t *bindFindExisting( byte srcEpInt,
                                     zAddrType_t *dstShortAddr, byte dstEpInt );

/*
 *  Remove bind(s) associated to a address (source or destination)
 */
extern void bindRemoveDev( zAddrType_t *shortAddr);

/*
 *  Remove bind(s) associated to a address (source)
 */
extern void bindRemoveSrcDev( uint8 ep );

/*
 * Calculate the number items this device is bound to.
 */
extern byte bindNumBoundTo( zAddrType_t *devAddr, byte devEpInt, byte srcMode );

/*
 * Count the number of reflections.
 */
extern uint16 bindNumReflections( uint8 ep, uint16 clusterID );

/*
 * Finds the binding entry for the source address,
 * endpoint and clusterID passed in as a parameter.
 */
extern BindingEntry_t *bindFind( uint8 ep, uint16 clusterID, uint8 skipping );

/*
 * Lookup a binding entry by specific Idx, if none is found
 * clears the BINDING user from Address Manager.
 */
extern void bindAddressClear( uint16 dstIdx );

/*
 * Processes the Hand Binding Timeout.
 */
extern void nwk_HandBindingTimeout( void );

/*
 * Initialize Binding Table NV Item
 */
extern byte BindInitNV( void );

/*
 * Initialize Binding Table NV Item
 */
extern void BindSetDefaultNV( void );

/*
 * Restore Binding Table from NV
 */
extern uint16 BindRestoreFromNV( void );

/*
 * Write Binding Table out to NV
 */
extern void BindWriteNV( void );

/*
 * Update network address in binding table
 */
extern void bindUpdateAddr( uint16 oldAddr, uint16 newAddr );

/*
 * This function is used to Add an entry to the binding table
 */
extern BindingEntry_t *bindAddEntry( byte srcEpInt,
                                  zAddrType_t *dstAddr, byte dstEpInt,
                                  byte numClusterIds, uint16 *clusterIds );

/*
 * This function returns the number of binding table entries
 */
extern uint16 bindNumOfEntries( void );

/*
 *  This function returns the number of binding entries
 *          possible and used.
 */
extern void bindCapacity( uint16 *maxEntries, uint16 *usedEntries );


/*
 *  This function returns the bind address index
 */
extern uint16 bindAddrIndexGet( zAddrType_t* addr );

/*********************************************************************
 * FUNCTION POINTERS
 */

/*
 * This function is used to Add an entry to the binding table
 */
extern BindingEntry_t *(*pbindAddEntry)( byte srcEpInt,
                                  zAddrType_t *dstAddr, byte dstEpInt,
                                  byte numClusterIds, uint16 *clusterIds );

/*
 * This function returns the number of binding table entries
 */
extern uint16 (*pbindNumOfEntries)( void );

/*
 *  Remove bind(s) associated to a address (source or destination)
 */
extern void (*pbindRemoveDev)( zAddrType_t *Addr );

/*
 * Initialize Binding Table NV Item
 */
extern byte (*pBindInitNV)( void );

/*
 * Initialize Binding Table NV Item
 */
extern void (*pBindSetDefaultNV)( void );

/*
 *  Restore binding table from NV
 */
extern uint16 (*pBindRestoreFromNV)( void );

/*
 *  Write binding table to NV
 */
extern void (*pBindWriteNV)( void );

/*
 * Convert address manager index to zAddrType_t for an extended address
 */
extern uint8 bindingAddrMgsHelperConvert( uint16 idx, zAddrType_t *addr );

/*
 * Convert address manager index to short address
 */
extern uint16 bindingAddrMgsHelperConvertShort( uint16 idx );

/*
 * Get a pointer to the Nth valid binding table entry.
 */
extern BindingEntry_t *GetBindingTableEntry( uint16 Nth );

/*********************************************************************
*********************************************************************/







#line 55 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\nwk\\nwk_globals.h"
#line 1 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\sys\\ZGlobals.h"
/**************************************************************************************************
  Filename:       nwk_globals.h
  Revised:        $Date: 2015-01-21 19:28:52 -0800 (Wed, 21 Jan 2015) $
  Revision:       $Revision: 41954 $

  Description:    User definable Z-Stack parameters.


  Copyright 2007-2015 Texas Instruments Incorporated. All rights reserved.

  IMPORTANT: Your use of this Software is limited to those specific rights
  granted under the terms of a software license agreement between the user
  who downloaded the software, his/her employer (which must be your employer)
  and Texas Instruments Incorporated (the "License"). You may not use this
  Software unless you agree to abide by the terms of the License. The License
  limits your use, and you acknowledge, that the Software may not be modified,
  copied or distributed unless embedded on a Texas Instruments microcontroller
  or used solely and exclusively in conjunction with a Texas Instruments radio
  frequency transceiver, which is integrated into your product. Other than for
  the foregoing purpose, you may not use, reproduce, copy, prepare derivative
  works of, modify, distribute, perform, display or sell this Software and/or
  its documentation for any purpose.

  YOU FURTHER ACKNOWLEDGE AND AGREE THAT THE SOFTWARE AND DOCUMENTATION ARE
  PROVIDED "AS IS" WITHOUT WARRANTY OF ANY KIND, EITHER EXPRESS OR IMPLIED,
  INCLUDING WITHOUT LIMITATION, ANY WARRANTY OF MERCHANTABILITY, TITLE,
  NON-INFRINGEMENT AND FITNESS FOR A PARTICULAR PURPOSE. IN NO EVENT SHALL
  TEXAS INSTRUMENTS OR ITS LICENSORS BE LIABLE OR OBLIGATED UNDER CONTRACT,
  NEGLIGENCE, STRICT LIABILITY, CONTRIBUTION, BREACH OF WARRANTY, OR OTHER
  LEGAL EQUITABLE THEORY ANY DIRECT OR INDIRECT DAMAGES OR EXPENSES
  INCLUDING BUT NOT LIMITED TO ANY INCIDENTAL, SPECIAL, INDIRECT, PUNITIVE
  OR CONSEQUENTIAL DAMAGES, LOST PROFITS OR LOST DATA, COST OF PROCUREMENT
  OF SUBSTITUTE GOODS, TECHNOLOGY, SERVICES, OR ANY CLAIMS BY THIRD PARTIES
  (INCLUDING BUT NOT LIMITED TO ANY DEFENSE THEREOF), OR OTHER SIMILAR COSTS.

  Should you have any questions regarding your right to use this Software,
  contact Texas Instruments Incorporated at www.TI.com.
**************************************************************************************************/








/*********************************************************************
 * INCLUDES
 */


/*********************************************************************
 * MACROS
 */




// Setup to work with the existing (old) compile flags
#line 69 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\sys\\ZGlobals.h"

// Use the following to macros to make device type decisions























   
   








#line 113 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\sys\\ZGlobals.h"

#line 123 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\sys\\ZGlobals.h"










/*********************************************************************
 * CONSTANTS
 */

// Values for ZCD_NV_LOGICAL_TYPE (zgDeviceLogicalType)




//#define DEVICE_LOGICAL_TYPE ZG_DEVICETYPE_COORDINATOR

// Default Device Logical Type


    // If capable, default to coordinator
#line 158 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\sys\\ZGlobals.h"

// Transmission retries numbers
#line 166 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\sys\\ZGlobals.h"

// NIB parameters
#line 177 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\sys\\ZGlobals.h"





















// Concentrator values
















// The hop count radius for concentrator route discoveries















// Backwards compatible - AMI changed name to SE




// APS Duplication Rejection Table Values
#line 246 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\sys\\ZGlobals.h"

// Child aging management default values
// Values are specified in table of nwk_globals.h module
//timeoutValue[15]
//    10, // 0	10 seconds
//     2, // 1	2 minutes
//     4, // 2	4 minutes
//     8, // 3	8 minutes
//    16, // 4	16 minutes
//    32, // 5	32 minutes
//    64, // 6	64 minutes
//   128, // 7	128 minutes
//   256, // 8	256 minutes
//   512, // 9	512 minutes
//  1024, // 10	1024 minutes
//  2048, // 11	2048 minutes
//  4096, // 12	4096 minutes
//  8192, // 13	8192 minutes
// 16384 // 14	16384 minutes
//
// This value is used by the parent ROUTER



   
   
//Timeout after which an EndDevice will be removed from from the indirect MAC messages queue
   // NOTE: End devices which poll rate is slower than this will not receive the leave request




// Value used by END DEVICE when sending End Device Timeout Request
// This is an index into table timeoutValue[] defined in nwk_globals.c




// Value used by END DEVICE when sending End Device Timeout Request




//--------------------------------------------------------------------
// Security modes
//--------------------------------------------------------------------





#line 308 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\sys\\ZGlobals.h"
//        #define ZG_SECURITY_MODE ZG_SECURITY_PRO_HIGH






//--------------------------------------------------------------------
// Security settings
//--------------------------------------------------------------------




#line 329 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\sys\\ZGlobals.h"

// Values for zgApsLinkKeyType



// Values for KeyAttributes



//Internal keyAttribute definitions




  
   



   
/*********************************************************************
 * TYPEDEFS
 */

/*********************************************************************
 * NWK GLOBAL VARIABLES
 */

extern uint32 zgPollRate;
extern uint32 zgSavedPollRate;
extern uint16 zgQueuedPollRate;
extern uint16 zgResponsePollRate;
extern uint16 zgRejoinPollRate;
extern uint32 zgDefaultRejoinBackoff;
extern uint32 zgDefaultRejoinScan;
// Variables for number of transmission retries
extern uint8 zgMaxDataRetries;
extern uint8 zgMaxPollFailureRetries;

extern uint32 zgDefaultChannelList;

extern uint8 zgStackProfile;

extern uint8 zgIndirectMsgTimeout;
extern uint8 zgSecurityMode;
extern uint8 zgSecurePermitJoin;
extern uint8 zgAllowRejoins;
extern uint8 zgAllowInstallCodes;
extern uint8 zgAllowRemoteTCPolicyChange;
extern uint8 zgApsTrustCenterAddr[];
extern uint8 zgRouteDiscoveryTime;
extern uint8 zgRouteExpiryTime;

extern uint8 zgExtendedPANID[];

extern uint8 zgMaxBcastRetires;
extern uint8 zgPassiveAckTimeout;
extern uint8 zgBcastDeliveryTime;

extern uint8 zgNwkMode;

extern uint8 zgConcentratorEnable;
extern uint8 zgConcentratorDiscoveryTime;
extern uint8 zgConcentratorRadius;
extern uint8 zgConcentratorRC;
extern uint8 zgNwkSrcRtgExpiryTime;

extern uint8 zgRouterOffAssocCleanup;

extern uint8 zgNwkLeaveRequestAllowed;

extern uint8 zgNwkParentInformation;

extern uint8 zgNwkEndDeviceTimeoutDefault;

extern uint8 zgNwkEndDeviceLeaveTimeoutDefault;

extern uint8 zgEndDeviceTimeoutValue;

extern uint8 zgEndDeviceConfiguration;

extern uint8 zgChildAgingEnable;

extern uint8 zTouchLinkNwkStartRtr;

/*********************************************************************
 * APS GLOBAL VARIABLES
 */

extern uint8  zgApscMaxFrameRetries;
extern uint16 zgApscAckWaitDurationPolled;
extern uint8  zgApsAckWaitMultiplier;
extern uint16 zgApsDefaultMaxBindingTime;
extern uint8  zgApsUseExtendedPANID[8];
extern uint8  zgApsUseInsecureJoin;
extern uint8  zgApsNonMemberRadius;

extern uint16 zgApscDupRejTimeoutInc;
extern uint8  zgApscDupRejTimeoutCount;
extern uint16 zgApsMinDupRejTableSize;

/*********************************************************************
 * SECURITY GLOBAL VARIABLES
 */

extern uint8 zgPreConfigKeys;
extern uint8 zgApsLinkKeyType;
extern uint8 zgUseDefaultTCLK;

#line 447 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\sys\\ZGlobals.h"

extern uint8 zgApsAllowR19Sec;
extern uint8 zgSwitchCoordKey;
extern uint8 zgSwitchCoordKeyIndex;

/*********************************************************************
 * ZDO GLOBAL VARIABLES
 */

extern uint16 zgConfigPANID;
extern uint8  zgDeviceLogicalType;
extern uint8  zgNwkMgrMinTransmissions;

extern uint8 zgZdoDirectCB;


/*********************************************************************
 * APPLICATION VARIABLES
 */

extern uint8 zgNwkMgrMode;

/*********************************************************************
 * FUNCTIONS
 */

/*
 * Initialize the Z-Stack Globals.
 */
extern uint8 zgInit( void );

/*
 * Initialize the RAM Items table with NV values.
 *    setDefault - if calling from outside ZGlobal use FALSE.
 */
extern void zgInitItems( uint8 setDefault );

/*
 * Get Startup Options (ZCD_NV_STARTUP_OPTION NV Item)
 */
extern uint8 zgReadStartupOptions( void );

/*
 * Write Startup Options (ZCD_NV_STARTUP_OPTION NV Item)
 *
 *      action - ZG_STARTUP_SET set bit, ZG_STARTUP_CLEAR to clear bit.
 *               The set bit is an OR operation, and the clear bit is an
 *               AND ~(bitOptions) operation.
 *      bitOptions - which bits to perform action on:
 *                      ZCD_STARTOPT_DEFAULT_CONFIG_STATE
 *                      ZDC_STARTOPT_DEFAULT_NETWORK_STATE
 *
 * Returns - ZSUCCESS if successful
 */
extern uint8 zgWriteStartupOptions( uint8 action, uint8 bitOptions );

/*
 *  Set RAM variables from set-NV, if it exist in the zgItemTable
 */
extern void zgSetItem( uint16 id, uint16 len, void *buf );

/*********************************************************************
*********************************************************************/




#line 56 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\nwk\\nwk_globals.h"

/*********************************************************************
 * MACROS
 */

/*********************************************************************
 * CONSTANTS
 */




// If ZIGBEEPRO is defined - define all the features for Zigbee Pro
#line 82 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\nwk\\nwk_globals.h"


  // The PANID Conflict feature is mandatory for both 2007 and 2007 PRO.
  // So, it will be ON all the time (except sleeping end devices).






  // The Frequency Agility feature is mandatory for both 2007 and 2007 PRO.
  // So, it will be ON all the time for routers.






  // Make Frequency Agility to look for all MAC errors for Certification test
  // by setting the following to TRUE. The default value is FALSE meaning
  // that only ZMacChannelAccessFailure error code will trigger a scan.





// Controls the operational mode of network




// Controls various stack parameter settings






// Channel mask













#line 145 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\nwk\\nwk_globals.h"

#line 183 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\nwk\\nwk_globals.h"

// Zigbee protocol version






// Status and error codes for extra information
#line 199 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\nwk\\nwk_globals.h"






// Indicate whether incoming NWK frames must be all checked for freshness
// when the memory for incoming frame counts is exceeded




// Indicate whether to use Multicast in NIB value




// Maximum number in tables


                                    // Assoc/Device list.


// Don't change this value to set the number of devices.  Change
//  NWK_MAX_DEVICE_LIST above




// Number of End Devices that will be stored in the SrcMatch and NotMyChildList lists
// when aged out by the Child Table Management process
// It is recommemded to keep this values to a fraction of gNWK_MAX_SLEEPING_END_DEVICES value
// which is the value of the table in the radio


// Number of reserved places for router and end device children, to be used in stochastic addressing.
#line 241 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\nwk\\nwk_globals.h"

#line 249 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\nwk\\nwk_globals.h"





// Maxiumum number of REFLECTOR address entries










// Maxiumum number of secure partners(Commercial mode only).

// Adding 5 entries to allow up to 5 legacy devices join concurrently when the rest of the 
// table is filled with ZigBee 3.0 devices, binding table related addresses, association 
// table related addresses, etc. the usage of these 5 entries is just temporary during joining
// of the legacy devices. A few seconds (BDB_DEFAULT_TC_NODE_JOIN_TIMEOUT) after they joined,
// these entries are released and can be used for joining more legacy devices.





  
// Maximum number of addresses managed by the Address Manager





// Network PAN Coordinator Address


// Network Addressing modes
























  // in milliseconds. The time limited to one MTO RReq (Concentrator Announce)




  // The number of seconds a MTO routing entry will last. Default to not expiring.









                                                // last received address conflict
                                                // report (network status command)










// This the size of the conflicted address table
// Scale it up if the size of the network is over 100 nodes




// Maximum number of relays in source routing













  // the default network radius set twice the value of <nwkMaxDepth>







// ZigBee Alliance Pre-configured Distributed Link Key (for Distributed networks)


                            
// ZigBee Alliance Pre-configured TC Link Key - 'ZigBeeAlliance09' (for Centralized networks)



//Define the number of network security material entries that this device can have.
//The first MAX_NWK_SEC_MATERIAL_TABLE_ENTRIES-1 networks will be stored, while the last 
//will be used for the remaining networks joined







/*********************************************************************
 * TYPEDEFS
 */



  typedef uint8 neighborTableIndex_t;





  typedef uint8 deviceTableIndex_t;





  typedef uint8 rtgTableIndex_t;





  typedef uint8 srcRtgTableIndex_t;





  typedef uint8 rreqTableIndex_t;





  typedef uint8 bindTableIndex_t;





  typedef uint8 bcastTableIndex_t;








/*********************************************************************
 * NWK GLOBAL VARIABLES
 */

// Variables for MAX data buffer levels
extern const byte gNWK_MAX_DATABUFS_WAITING;
extern const byte gNWK_MAX_DATABUFS_SCHEDULED;
extern const byte gNWK_MAX_DATABUFS_CONFIRMED;
extern const byte gNWK_MAX_DATABUFS_TOTAL;

extern const byte gNWK_INDIRECT_CNT_RTG_TMR;
extern const byte gNWK_INDIRECT_MSG_MAX_PER;
extern const byte gNWK_INDIRECT_MSG_MAX_ALL;

extern const neighborTableIndex_t gMAX_NEIGHBOR_ENTRIES;

extern const rtgTableIndex_t gMAX_RTG_ENTRIES;
extern const srcRtgTableIndex_t gMAX_RTG_SRC_ENTRIES;
extern const rreqTableIndex_t gMAX_RREQ_ENTRIES;

extern const uint16 gMTO_RREQ_LIMIT_TIME;
extern const uint8 gMTO_ROUTE_EXPIRY_TIME;

extern const uint8 gMAX_PASSIVE_ACK_CNT;

// Variables for MAX list size
extern const deviceTableIndex_t gNWK_MAX_DEVICE_LIST;

// Variables for MAX Sleeping End Devices
extern const uint8 gNWK_MAX_SLEEPING_END_DEVICES;

extern const uint8 gNWK_TREE_ALLOCATE_ROUTERADDR_FOR_ENDDEVICE;

extern const uint16 gNWK_MIN_ROUTER_CHILDREN;
extern const uint16 gNWK_MIN_ENDDEVICE_CHILDREN;

extern uint16 *Cskip;
extern byte CskipRtrs[];
extern byte CskipChldrn[];

extern byte gMIN_TREE_LQI;

extern const byte defaultKey[];





extern const byte defaultTCLinkKey[];

extern const uint8 gMAX_SOURCE_ROUTE;
extern uint16 rtgSrcRelayList[];

extern const bcastTableIndex_t gMAX_BCAST;

extern const byte gNWK_CONFLICTED_ADDR_EXPIRY_TIME;


extern const uint8 gNWK_FREQ_AGILITY_ALL_MAC_ERRS;

extern const uint8 gMAX_BROADCAST_QUEUED;

extern const uint8 gLINK_DOWN_TRIGGER;

extern const uint8 gGOOD_LINK_COST;

extern const uint8 gDEFAULT_ROUTE_REQUEST_RADIUS;

extern const uint8 gDEF_NWK_RADIUS;


extern const uint16 gLINK_STATUS_JITTER_MASK;


extern const uint8 gMAX_NOT_MYCHILD_DEVICES;

extern const uint32 timeoutValue[];

extern const uint32 gMAX_NWK_FRAMECOUNTER_CHANGES;






/*********************************************************************
 * APS GLOBAL VARIABLES
 */

// Variables for Binding Table
extern const bindTableIndex_t gNWK_MAX_BINDING_ENTRIES;
extern const uint8 gMAX_BINDING_CLUSTER_IDS;
extern const uint16 gBIND_REC_SIZE;

extern const uint8 gAPS_MAX_GROUPS;

extern uint8 gAPS_MAX_ENDDEVICE_BROADCAST_ENTRIES;

/*********************************************************************
 * GLOBAL VARIABLES - Statistics
 */

#line 544 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\nwk\\nwk_globals.h"

/*********************************************************************
 * FUNCTIONS
 */

/*
 * Init Global Variables
 */
extern void nwk_globals_init( void );
extern void NIB_init( void );

extern void nwk_Status( uint16 statusCode, uint16 statusValue );

extern uint16 nwk_adjustDelay( uint16 existingDelay, uint8 confirmStatus, uint16 bufOptions );

/*********************************************************************
*********************************************************************/







#line 53 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\nwk\\APSMEDE.h"





/******************************************************************************
 * MACROS
 */

/******************************************************************************
 * CONSTANTS
 */
// Frame control fields






















#line 99 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\nwk\\APSMEDE.h"

// Tx Options (bitmap values)

//#define APS_TX_OPTIONS_USE_NWK_KEY    0x0002u remove from spec
#line 110 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\nwk\\APSMEDE.h"

// APSDE header fields


// APSME CMD id index


// APS commands
#line 126 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\nwk\\APSMEDE.h"
   
// APSME CMD packet fields (APSME_CMD_TRANSPORT_KEY)
#line 135 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\nwk\\APSMEDE.h"













                                 


                         
   
   
// APSME CMD packet fields (APSME_CMD_UPDATE_DEVICE)
#line 162 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\nwk\\APSMEDE.h"







// APSME CMD packet fields (APSME_CMD_REMOVE_DEVICE)



// APSME CMD packet fields (APSME_CMD_REQUEST_KEY)





// APSME CMD packet fields (APSME_CMD_SWITCH_KEY)



// APSME CMD packet fields (APSME_CMD_TUNNEL)

//devtag.pro.security.remove
//      APSME_TUNNEL_AUX  9 //auxillary header(obsolete)



// APSME CMD packet fields (APSME_CMD_VERIFY_KEY)





// APSME CMD packet fields (APSME_CMD_CONFIRM_KEY)





// APSME Coordinator/Trust Center NWK addresses



  // The number of times the frame counter can change before
  // saving to NV




  // The number of times the frame counter can change before
  // saving to NV



/******************************************************************************
 * TYPEDEFS
 */

// AIB item Ids
typedef enum
{
  apsAddressMap = 0xA0,

  // Proprietary Items
  apsMaxBindingTime,
  apsBindingTable,
  apsNumBindingTableEntries,
  apsUseExtendedPANID,
  apsUseInsecureJoin,
  apsTrustCenterAddress = 0xAB,
  apsMAX_AIB_ITEMS  // Must be the last entry
} ZApsAttributes_t;

// Type of information being queried
typedef enum
{
  NWK_ADDR_LIST,
  EXT_ADDRESS,
  SIMPLE_DESC,
  NODE_DESC,
  POWER_DESC,
  SVC_MATCH
} APSME_query_t;



// Structure returned from APSME_GetRequest for apsBindingTable
typedef struct
{
  uint8 srcAddr[8]; // Src address
  byte srcEP;                   // Endpoint/interface of source device
  uint16 clusterID;             // Cluster ID
  zAddrType_t dstAddr;          // Destination address
  byte dstEP;                   // Endpoint/interface of dest device
} apsBindingItem_t;

typedef struct
{
  uint8 FrmCtrl;
  uint8 XtndFrmCtrl;
  uint8 DstEndPoint;
  uint8 SrcEndPoint;
  uint16 GroupID;
  uint16 ClusterID;
  uint16 ProfileID;
  uint16 macDestAddr;
  uint8 wasBroadcast;
  uint8 apsHdrLen;
  uint8 *asdu;
  uint8 asduLength;
  uint8 ApsCounter;
  uint8 transID;
  uint8 BlkCount;
  uint8 AckBits;
  uint16 macSrcAddr;
} aps_FrameFormat_t;

typedef struct
{
  uint16 tna; // tunnel network address
  uint8* dea; // destination extended address
} APSDE_FrameTunnel_t;

// APS Data Service Primitives
typedef struct
{
  zAddrType_t dstAddr;
  uint8       srcEP;
  uint8       dstEP;
  uint16      dstPanId;
  uint16      clusterID;
  uint16      profileID;
  uint16      asduLen;
  uint8*      asdu;
  uint16      txOptions;
  uint8       transID;
  uint8       discoverRoute;
  uint8       radiusCounter;
  uint8       apsCount;
  uint8       blkCount;
  uint8       apsRetries;
  uint8       nsduHandle;
} APSDE_DataReq_t;

typedef struct
{
  uint16 dstAddr;
  uint8  dstEP;
  uint8  srcEP;
  uint8  transID;
  uint8  status;
} APSDE_DataCnf_t;

typedef struct
{
  uint8 secure;
  uint8 addressingMode; // Helps to identify the exact length of the payload.
} APSDE_DataReqMTU_t;

// APS Security Related Primitives
typedef struct
{
  uint16               dstAddr;
  uint8                keyType;
  uint8                keySeqNum;
  uint8*               key;
  uint8*               extAddr;
  uint8                initiator;
  uint8                apsSecure;
  uint8                nwkSecure;
  APSDE_FrameTunnel_t* tunnel;
} APSME_TransportKeyReq_t;

typedef struct
{
  uint16 srcAddr;
  uint8  keyType;
  uint8  keySeqNum;
  uint8* key;
  uint8* dstExtAddr;
  uint8* srcExtAddr;
  uint8  initiator;
  uint8  secure;
} APSME_TransportKeyInd_t;

typedef struct
{
  uint16 dstAddr;
  uint16 devAddr;
  uint8* devExtAddr;
  uint8  status;
  uint8  apsSecure;
} APSME_UpdateDeviceReq_t;

typedef struct
{
  uint16 srcAddr;
  uint8* devExtAddr;
  uint16 devAddr;
  uint8  status;
} APSME_UpdateDeviceInd_t;

typedef struct
{
  uint16 parentAddr;
  uint8* childExtAddr;
  uint8  apsSecure;
} APSME_RemoveDeviceReq_t;

typedef struct
{
  uint16 srcAddr;
  uint8* childExtAddr;
} APSME_RemoveDeviceInd_t;

typedef struct
{
  uint8  dstAddr;
  uint8  keyType;
  uint8* partExtAddr;
} APSME_RequestKeyReq_t;

typedef struct
{
  uint16 srcAddr;
  uint8  keyType;
  uint8* partExtAddr;
} APSME_RequestKeyInd_t;

typedef struct
{
  uint16 dstAddr;
  uint8  keySeqNum;
  uint8  apsSecure;
} APSME_SwitchKeyReq_t;

typedef struct
{
  uint16 srcAddr;
  uint8  keySeqNum;
} APSME_SwitchKeyInd_t;

typedef struct
{
  uint8* tcExtAddr;
  uint8  keyType;
} APSME_VerifyKeyReq_t;

typedef struct
{
  uint16 srcAddr;
  uint8  keyType;
  uint8* partExtAddr;
  uint8* receivedInitiatorHashValue;
} APSME_VerifyKeyInd_t;

typedef struct
{
  uint16 dstAddr;
  uint8  status;
  uint8* dstExtAddr;
  uint8  keyType;
} APSME_ConfirmKeyReq_t;

typedef struct
{
  uint16 srcAddr;
  uint8  status;
  uint8* srcExtAddr;
  uint8  keyType;
} APSME_ConfirmKeyInd_t;

// APS Incoming Command Packet
typedef struct
{
  osal_event_hdr_t hdr;
  uint8*           asdu;
  uint8            asduLen;
  uint8            secure;
  uint16           nwkAddr;
  uint8            nwkSecure;
} APSME_CmdPkt_t;

typedef struct
{
  uint8  key[16];
  uint32 txFrmCntr;
  uint32 rxFrmCntr;
} APSME_LinkKeyData_t;

typedef struct
{
  uint8   frmCtrl;
  uint8   xtndFrmCtrl;
  uint8   srcEP;
  uint8   dstEP;
  uint16  groupID;
  uint16  clusterID;
  uint16  profileID;
  uint8   asduLen;
  uint8*  asdu;
  uint8   hdrLen;
  uint8   apsCounter;
  uint8   transID;
  uint8   blkCount;
  uint8   ackBits;
} APSDE_FrameData_t;

typedef struct
{
  uint8  frmCtrl;
  uint8  xtndFrmCtrl;
  uint8  srcEP;
  uint8  dstEP;
  uint16 clusterID;
  uint16 profileID;
  uint8  asduLen;
  uint16 dstAddr;
  uint8  transID;
  uint8  apsCounter;
} APSDE_StoredFrameData_t;

typedef struct
{
//ZMacDataReq_t     mfd;
  NLDE_FrameData_t  nfd;
  APSDE_FrameData_t afd;
} APSDE_FrameFormat_t;

typedef struct
{
  uint16               dstAddr;
  uint8                frmCtrl;
  uint8                xtndFrmCtrl;
  uint8                asduLen;
  uint8                nwkSecure;
  APSDE_FrameTunnel_t* tunnel;
} APSDE_FrameAlloc_t;

typedef struct
{
  //input
  APSDE_FrameAlloc_t   fa;

  //output
  APSDE_FrameFormat_t* aff;
  SSP_Info_t*          si;
  uint8                status;
} APSDE_FrameBlk_t;

typedef struct
{
  uint32 txFrmCntr;
  uint32 rxFrmCntr;
  uint8  extAddr[8];
  uint8  keyAttributes;
  uint8  keyType;
  uint8  SeedShift_IcIndex;    //For Unique key this is the number of shifts, for IC this is the offset on the NvId index
} APSME_TCLKDevEntry_t;

typedef struct
{
  uint32 txFrmCntr;
  uint32 rxFrmCntr;
  uint8  pendingFlag;
} APSME_ApsLinkKeyFrmCntr_t;

typedef struct
{
  uint32 txFrmCntr;
  uint32 rxFrmCntr;
  uint8  pendingFlag;
} APSME_TCLinkKeyFrmCntr_t;

// Function pointer prototype to preprocess messages before calling NWK layer
typedef void (*apsPreProcessDataReq_t)( APSDE_FrameBlk_t *blk );

/******************************************************************************
 * GLOBAL VARIABLES
 */
// Store Frame Counters in RAM and update NV periodically
extern APSME_ApsLinkKeyFrmCntr_t ApsLinkKeyFrmCntr[];
extern APSME_TCLinkKeyFrmCntr_t TCLinkKeyFrmCntr[];

/******************************************************************************
 * APS Data Service
 *   APSDE-DATA
 */

/*
 * This function requests the transfer of data from the next higher layer
 * to a single peer entity.
 */
extern ZStatus_t APSDE_DataReq( APSDE_DataReq_t* req );

/*
 * This function requests the MTU(Max Transport Unit) of the APS Data Service
 */
extern uint8 APSDE_DataReqMTU( APSDE_DataReqMTU_t* fields );

/*
 * This function reports the results of a request to transfer a data
 * PDU (ASDU) from a local higher layer entity to another single peer entity.
 */
extern void APSDE_DataConfirm( nwkDB_t *rec, ZStatus_t Status );
extern void APSDE_DataCnf( APSDE_DataCnf_t* cnf );

/*
 * This function indicates the transfer of a data PDU (ASDU) from the
 * APS sub-layer to the local application layer entity.
 */
extern void APSDE_DataIndication( aps_FrameFormat_t *aff, zAddrType_t *SrcAddress,
                                uint16 SrcPanId, NLDE_Signal_t *sig, uint8 nwkSeqNum,
                                byte SecurityUse, uint32 timestamp, uint8 radius  );

/******************************************************************************
 * APS Management Service
 *   APSME-BIND
 *   APSME-UNBIND
 */

/*
 * This function allows the next higher layer to request to bind two devices together
 * either by proxy or directly, if issued on the coordinator.
 *
 * NOTE: The APSME-BIND.confirm is returned by this function and is not a
 *       seperate callback function.
 */
extern ZStatus_t APSME_BindRequest( byte SrcEndpInt, uint16 ClusterId,
                                   zAddrType_t *DstAddr, byte DstEndpInt);

/*
 * This function allows the next higher layer to request to unbind two devices
 * either by proxy or directly, if issued on the coordinator.
 *
 * NOTE: The APSME-UNBIND.confirm is returned by this function and is not a
 *       seperate callback function.
 */
extern ZStatus_t APSME_UnBindRequest( byte SrcEndpInt,
                            uint16 ClusterId, zAddrType_t *DstAddr, byte DstEndpInt);

/*
 * This function allows the next higher layer to read the value of an attribute
 * from the AIB (APS Information Base)
 */
extern ZStatus_t APSME_GetRequest( ZApsAttributes_t AIBAttribute,
                                    uint16 Index, byte *AttributeValue );

/*
 * This function allows the next higher layer to write the value of an attribute
 * into the AIB (APS Information Base)
 */
extern ZStatus_t APSME_SetRequest( ZApsAttributes_t AIBAttribute,
                                    uint16 Index, byte *AttributeValue );

/*
 * This function gets the EXT address based on the NWK address.
 */
extern uint8 APSME_LookupExtAddr( uint16 nwkAddr, uint8* extAddr );

/*
 * This function gets the NWK address based on the EXT address.
 */
extern uint8 APSME_LookupNwkAddr( uint8* extAddr, uint16* nwkAddr );

#line 644 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\nwk\\APSMEDE.h"

/*
 * Set the Preprocess function pointer.  The APS Layer will call this function
 * right before calling APSDE_FrameSend() [setup function that calls NLDE_DataReq()].
 */
extern void APSDE_SetPreProcessFnp( apsPreProcessDataReq_t pfnCB );


/******************************************************************************
 * APS Incoming Command Packet Handler
 */

/*
 * APSME_CmdPkt handles APS CMD packets.
 */
extern void APSME_CmdPkt( APSME_CmdPkt_t* pkt );

/******************************************************************************
 * APS Frame Allocation And Routing
 */

/*
 * APSDE_FrameAlloc allocates an APS frame.
 */
extern void APSDE_FrameAlloc( APSDE_FrameBlk_t* blk );

/*
 * APSDE_FrameSend sends an APS frame.
 */
extern void APSDE_FrameSend( APSDE_FrameBlk_t* blk );

/*
 * APSME_HoldDataRequests holds all data request for a timeout.
 */
void APSME_HoldDataRequests( uint16 holdTime );

/******************************************************************************
 * APS Security Related Functions
 */

/*
 * APSME_FrameSecurityRemove removes security from APS frame.
 */
extern ZStatus_t APSME_FrameSecurityRemove(uint16             srcAddr,
                                           aps_FrameFormat_t* aff);

/*
 * APSME_FrameSecurityApply applies security to APS frame.
 */
extern ZStatus_t APSME_FrameSecurityApply(uint16             dstAddr,
                                          aps_FrameFormat_t* aff);

/*
 * Configure APS security mode
 */
extern void APSME_SecurityNM( void );   // NULL MODE        - NO SECURITY
extern void APSME_SecurityRM_ED( void );// RESIDENTIAL MODE - END DEVICE
extern void APSME_SecurityRM_RD( void );// RESIDENTIAL MODE - ROUTER DEVICE
extern void APSME_SecurityRM_CD( void );// RESIDENTIAL MODE - COORD DEVICE
extern void APSME_SecurityCM_ED( void );// COMMERCIAL MODE  - END DEVICE
extern void APSME_SecurityCM_RD( void );// COMMERCIAL MODE  - ROUTER DEVICE
extern void APSME_SecurityCM_CD( void );// COMMERCIAL MODE  - COORD DEVICE

/******************************************************************************
 * APS Security Service Primitives - API, NHLE Calls Routines
 *
 *   APSME_TransportKeyReq
 *   APSME_UpdateDeviceReq
 *   APSME_RemoveDeviceReq
 *   APSME_RequestKeyReq
 *   APSME_SwitchKeyReq
 *   APSME_ConfirmKeyReq    // added for confirm key service
 */

/*
 * APSME_TransportKeyReq primitive.
 */
extern ZStatus_t APSME_TransportKeyReq( APSME_TransportKeyReq_t* req );

/*
 * APSME_UpdateDeviceReq primitive.
 */
extern ZStatus_t APSME_UpdateDeviceReq( APSME_UpdateDeviceReq_t* req );

/*
 * APSME_RemoveDeviceReq primitive.
 */
extern ZStatus_t APSME_RemoveDeviceReq( APSME_RemoveDeviceReq_t* req );

/*
 * APSME_RequestKeyReq primitive.
 */
extern ZStatus_t APSME_RequestKeyReq( APSME_RequestKeyReq_t* req );

/*
 * APSME_SwitchKeyReq primitive.
 */
extern ZStatus_t APSME_SwitchKeyReq( APSME_SwitchKeyReq_t* req );

/*
 * APSME_VerifyKeyReq_t primitive.
 */
extern ZStatus_t APSME_VerifyKeyReq( APSME_VerifyKeyReq_t* req );

/*
 * APSME_SwitchKeyReq primitive.
 */
extern ZStatus_t APSME_ConfirmKeyReq( APSME_ConfirmKeyReq_t* req );

/******************************************************************************
 * APS Security Primitive Stubs - API, NHLE Implements Callback Stubs
 *
 *   APSME_TransportKeyInd
 *   APSME_UpdateDeviceInd
 *   APSME_RemoveDeviceInd
 *   APSME_RequestKeyInd
 *   APSME_SwitchKeyInd
 */

/*
 * APSME_TransportKeyInd primitive.
 */
extern void APSME_TransportKeyInd( APSME_TransportKeyInd_t* ind );

/*
 * APSME_UpdateDeviceInd primitive.
 */
extern void APSME_UpdateDeviceInd( APSME_UpdateDeviceInd_t* ind );

/*
 * APSME_RemoveDeviceInd primitive.
 */
extern void APSME_RemoveDeviceInd( APSME_RemoveDeviceInd_t* ind );

/*
 * APSME_RequestKeyInd primitive.
 */
extern void APSME_RequestKeyInd( APSME_RequestKeyInd_t* ind );

/*
 * APSME_SwitchKeyInd primitive.
 */
extern void APSME_SwitchKeyInd( APSME_SwitchKeyInd_t* ind );

/*
 * APSME_VerifyKeyInd primitive.
 */
extern void APSME_VerifyKeyInd( APSME_VerifyKeyInd_t* ind );

/*
 * APSME_ConfirmKeyInd primitive.
 */
extern void APSME_ConfirmKeyInd( APSME_ConfirmKeyInd_t* apsmeInd );


/*
 * APSME_EraseICEntry
 */
extern void APSME_EraseICEntry(uint8 *IcIndex);

/*
 * APSME_AddTCLinkKey Interface to add TC link key derived from install codes.
 */
extern ZStatus_t APSME_AddTCLinkKey(uint8* pTCLinkKey, uint8* pExt);

/*
 * APSME_SetDefaultKey Interface to set the centralized default key to defaultTCLinkKey
 */
extern ZStatus_t APSME_SetDefaultKey(void);

/*
 * APSME_SearchTCLinkKeyEntry Interface search for the TCLK entry
 */
extern uint16 APSME_SearchTCLinkKeyEntry(uint8 *pExt,uint8* found, APSME_TCLKDevEntry_t* tcLinkKeyAddrEntry);
/******************************************************************************
 * APS Security Support - NHLE Implements Callback Stubs
 *
 *   APSME_LinkKeySet
 *   APSME_LinkKeyNVIdGet
 *   APSME_KeyFwdToChild
 */

/*
 * APSME_LinkKeySet stub.
 */
extern ZStatus_t APSME_LinkKeySet( uint8* extAddr, uint8* key );


/*
 * APSME_LinkKeyNVIdGet stub.
 */
extern ZStatus_t APSME_LinkKeyNVIdGet(uint8* extAddr, uint16 *pKeyNvId);

/*
 * APSME_IsLinkKeyValid stub.
 */
extern uint8 APSME_IsLinkKeyValid(uint8* extAddr);

/*
 * APSME_KeyFwdToChild stub.
 */
extern uint8 APSME_KeyFwdToChild( APSME_TransportKeyInd_t* ind );

/*
 * APSME_IsDistributedSecurity - Is APS configured for distributed secrity network
 * (not Trust Center protected).
 *    Use with ZG_SECURITY_SE_STANDARD
 */
extern uint8 APSME_IsDistributedSecurity( void );



/******************************************************************************
******************************************************************************/







#line 54 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\af\\AF.h"

/*********************************************************************
 * CONSTANTS
 */








                                                  // (route discovery preformed for initiating device)





// Backwards support for afAddOrSendMessage / afFillAndSendMessage.



// Default Radius Count value


/*********************************************************************
 * Node Descriptor
 */


typedef struct
{
  uint8 len;     // Length of string descriptor
  uint8 desc[16];
} UserDescriptorFormat_t;

// Node Logical Types




// Node Frequency Band - bit map




// Node MAC Capabilities - bit map
//   Use CAPINFO_ALTPANCOORD, CAPINFO_DEVICETYPE_FFD,
//       CAPINFO_DEVICETYPE_RFD, CAPINFO_POWER_AC,
//       and CAPINFO_RCVR_ON_IDLE from NLMEDE.h

// Node Descriptor format structure
typedef struct
{
  uint8 LogicalType:3;
  uint8 ComplexDescAvail:1;  /* AF_V1_SUPPORT - reserved bit. */
  uint8 UserDescAvail:1;     /* AF_V1_SUPPORT - reserved bit. */
  uint8 Reserved:3;
  uint8 APSFlags:3;
  uint8 FrequencyBand:5;
  uint8 CapabilityFlags;
  uint8 ManufacturerCode[2];
  uint8 MaxBufferSize;
  uint8 MaxInTransferSize[2];
  uint16 ServerMask;
  uint8 MaxOutTransferSize[2];
  uint8 DescriptorCapability;
} NodeDescriptorFormat_t;

// Bit masks for the ServerMask.
#line 131 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\af\\AF.h"


/*********************************************************************
 * Node Power Descriptor
 */

// Node Current Power Modes (CURPWR)
// Receiver permanently on or sync with coordinator beacon.

// Receiver automatically comes on periodically as defined by the
// Node Power Descriptor.

// Receiver comes on when simulated, eg by a user pressing a button.


// Node Available Power Sources (AVAILPWR) - bit map
//   Can be used for AvailablePowerSources or CurrentPowerSource




// Power Level





// Node Power Descriptor format structure
typedef struct
{
  unsigned int PowerMode:4;
  unsigned int AvailablePowerSources:4;
  unsigned int CurrentPowerSource:4;
  unsigned int CurrentPowerSourceLevel:4;
} NodePowerDescriptorFormat_t;

/*********************************************************************
 * Simple Descriptor
 */

// AppDevVer values


// AF_V1_SUPPORT AppFlags - bit map


// AF-AppFlags - bit map




typedef uint16  cId_t;
// Simple Description Format Structure
typedef struct
{
  uint8          EndPoint;
  uint16         AppProfId;
  uint16         AppDeviceId;
  uint8          AppDevVer:4;
  uint8          Reserved:4;             // AF_V1_SUPPORT uses for AppFlags:4.
  uint8          AppNumInClusters;
  cId_t         *pAppInClusterList;
  uint8          AppNumOutClusters;
  cId_t         *pAppOutClusterList;
} SimpleDescriptionFormat_t;

/*********************************************************************
 * AF Message Format
 */

// Frame Types









// Generalized MSG Command Format
typedef struct
{
  uint8   TransSeqNumber;
  uint16  DataLength;              // Number of bytes in TransData
  uint8  *Data;
} afMSGCommandFormat_t;

typedef enum
{
  noLatencyReqs,
  fastBeacons,
  slowBeacons
} afNetworkLatencyReq_t;

/*********************************************************************
 * Endpoint  Descriptions
 */

typedef enum
{
  afAddrNotPresent = AddrNotPresent,
  afAddr16Bit      = Addr16Bit,
  afAddr64Bit      = Addr64Bit,
  afAddrGroup      = AddrGroup,
  afAddrBroadcast  = AddrBroadcast
} afAddrMode_t;

typedef struct
{
  union
  {
    uint16      shortAddr;
    ZLongAddr_t extAddr;
  } addr;
  afAddrMode_t addrMode;
  uint8 endPoint;
  uint16 panId;  // used for the INTER_PAN feature
}  afAddrType_t;


typedef struct
{
  osal_event_hdr_t hdr;     /* OSAL Message header */
  uint16 groupId;           /* Message's group ID - 0 if not set */
  uint16 clusterId;         /* Message's cluster ID */
  afAddrType_t srcAddr;     /* Source Address, if endpoint is STUBAPS_INTER_PAN_EP,
                               it's an InterPAN message */
  uint16 macDestAddr;       /* MAC header destination short address */
  uint8 endPoint;           /* destination endpoint */
  uint8 wasBroadcast;       /* TRUE if network destination was a broadcast address */
  uint8 LinkQuality;        /* The link quality of the received data frame */
  uint8 correlation;        /* The raw correlation value of the received data frame */
  int8  rssi;               /* The received RF power in units dBm */
  uint8 SecurityUse;        /* deprecated */
  uint32 timestamp;         /* receipt timestamp from MAC */
  uint8 nwkSeqNum;          /* network header frame sequence number */
  afMSGCommandFormat_t cmd; /* Application Data */
  uint16 macSrcAddr;        /* MAC header source short address */
  uint8 radius;
} afIncomingMSGPacket_t;

typedef struct
{
  osal_event_hdr_t hdr;
  uint8 endpoint;
  uint8 transID;
} afDataConfirm_t;

// Reflect Error Message - sent when there is an error occurs
// during a reflected message.
typedef struct
{
  osal_event_hdr_t hdr;  // hdr.status contains the error indication (ie. ZApsNoAck)
  uint8 endpoint;        // destination endpoint
  uint8 transID;         // transaction ID of sent message
  uint8 dstAddrMode;     // destination address type: 0 - short address, 1 - group address
  uint16 dstAddr;        // destination address - depends on dstAddrMode
} afReflectError_t;

// Endpoint Table - this table is the device description
// or application registration.
// There will be one entry in this table for every
// endpoint defined.
typedef struct
{
  uint8 endPoint;
  uint8 epType;
  uint8 *task_id;  // Pointer to location of the Application task ID.
  SimpleDescriptionFormat_t *simpleDesc;
  afNetworkLatencyReq_t latencyReq;
} endPointDesc_t;

// Typedef for callback function to retrieve an endpoints
//   descriptors, contained in the endpoint descriptor.
//   This will allow an application to dynamically change
//   the descriptor and not use the RAM/ROM.
typedef void *(*pDescCB)( uint8 type, uint8 endpoint );

// Typedef for callback function to control the AF transaction ID
//   used when sending messages.
//   This allows the application to verify if the transaction ID
//   is not duplicated of a pending message.
typedef void (*pApplCB)( APSDE_DataReq_t *req );

// Descriptor types used in the above callback



// Bit definitions for epList_t flags.
typedef enum
{
  eEP_AllowMatch = 1,
  eEP_NotUsed
} eEP_Flags;

typedef struct {
  uint8 frameDelay;
  uint8 windowSize;
} afAPSF_Config_t;

typedef struct _epList_t {
  struct _epList_t *nextDesc;
  endPointDesc_t *epDesc;
  pDescCB  pfnDescCB;     // Don't use if this function pointer is NULL.
  afAPSF_Config_t apsfCfg;
  eEP_Flags flags;
  pApplCB pfnApplCB;    // Don't use it if it has not been set to a valid function pointer by the application
} epList_t;

/*********************************************************************
 * TYPEDEFS
 */







typedef ZStatus_t afStatus_t;

typedef struct
{
  uint8              kvp;
  APSDE_DataReqMTU_t aps;
} afDataReqMTU_t;

/*********************************************************************
 * Globals
 */

extern epList_t *epList;

/*********************************************************************
 * FUNCTIONS
 */

 /*
  * afInit - Initialize the AF.
  */
  //extern void afInit( void );


 /*
  * afRegisterExtended - Register an Application's EndPoint description
  *           with a callback function for descriptors and
  *           with an Application callback function to control
  *           the AF transaction ID.
  *
  */
  extern epList_t *afRegisterExtended( endPointDesc_t *epDesc, pDescCB descFn, pApplCB applFn );

 /*
  * afRegister - Register an Application's EndPoint description.
  *
  */
  extern afStatus_t afRegister( endPointDesc_t *epDesc );

 /*
  * afDelete - Delete an Application's EndPoint descriptor and frees the memory.
  *
  */
  extern afStatus_t afDelete( uint8 EndPoint );

 /*
  * afDataConfirm - APS will call this function after a data message
  *                 has been sent.
  */
  extern void afDataConfirm( uint8 endPoint, uint8 transID, ZStatus_t status );

 /*
  * afReflectError - APS will call this function for an error with a reflected data message.
  */
  extern void afReflectError( uint8 srcEP, uint8 dstAddrMode, uint16 dstAddr, uint8 dstEP,
                              uint8 transID, ZStatus_t status );

 /*
  * afIncomingData - APS will call this function when an incoming
  *                   message is received.
  */
  extern void afIncomingData( aps_FrameFormat_t *aff, zAddrType_t *SrcAddress, uint16 SrcPanId,
                       NLDE_Signal_t *sig, uint8 nwkSeqNum, uint8 SecurityUse, uint32 timestamp, uint8 radius );

  afStatus_t AF_DataRequest( afAddrType_t *dstAddr, endPointDesc_t *srcEP,
                             uint16 cID, uint16 len, uint8 *buf, uint8 *transID,
                             uint8 options, uint8 radius );


/*********************************************************************
 * @fn      AF_DataRequestSrcRtg
 *
 * @brief   Common functionality for invoking APSDE_DataReq() for both
 *          SendMulti and MSG-Send.
 *
 * input parameters
 *
 * @param  *dstAddr - Full ZB destination address: Nwk Addr + End Point.
 * @param  *srcEP - Origination (i.e. respond to or ack to) End Point Descr.
 * @param   cID - A valid cluster ID as specified by the Profile.
 * @param   len - Number of bytes of data pointed to by next param.
 * @param  *buf - A pointer to the data bytes to send.
 * @param  *transID - A pointer to a byte which can be modified and which will
 *                    be used as the transaction sequence number of the msg.
 * @param   options - Valid bit mask of Tx options.
 * @param   radius - Normally set to AF_DEFAULT_RADIUS.
 * @param   relayCnt - Number of devices in the relay list
 * @param   pRelayList - Pointer to the relay list
 *
 * output parameters
 *
 * @param  *transID - Incremented by one if the return value is success.
 *
 * @return  afStatus_t - See previous definition of afStatus_... types.
 */

afStatus_t AF_DataRequestSrcRtg( afAddrType_t *dstAddr, endPointDesc_t *srcEP,
                           uint16 cID, uint16 len, uint8 *buf, uint8 *transID,
                           uint8 options, uint8 radius, uint8 relayCnt,
                           uint16* pRelayList );

/*********************************************************************
 * Direct Access Functions - ZigBee Device Object
 */

 /*
  *	afFindEndPointDesc - Find the endpoint description entry from the
  *                      endpoint number.
  */
  extern endPointDesc_t *afFindEndPointDesc( uint8 endPoint );

 /*
  *	afFindSimpleDesc - Find the Simple Descriptor from the endpoint number.
  *   	  If return value is not zero, the descriptor memory must be freed.
  */
  extern uint8 afFindSimpleDesc( SimpleDescriptionFormat_t **ppDesc, uint8 EP );

 /*
  *	afDataReqMTU - Get the Data Request MTU(Max Transport Unit)
  */
  extern uint8 afDataReqMTU( afDataReqMTU_t* fields );

 /*
  *	afGetMatch - Get the action for the Match Descriptor Response
  *             TRUE allow match descriptor response
  */
  extern uint8 afGetMatch( uint8 ep );

 /*
  *	afSetMatch - Set the action for the Match Descriptor Response
  *             TRUE allow match descriptor response
  */
  extern uint8 afSetMatch( uint8 ep, uint8 action );

 /*
  *	afNumEndPoints - returns the number of endpoints defined.
  */
  extern uint8 afNumEndPoints( void );

 /*
  *	afEndPoints - builds an array of endpoints.
  */
  extern void afEndPoints( uint8 *epBuf, uint8 skipZDO );

 /*
  * afCopyAddress
  */
extern void afCopyAddress (afAddrType_t *afAddr, zAddrType_t *zAddr);

 /*
  *	afAPSF_ConfigGet - ascertain the fragmentation configuration for the specified EndPoint.
  */
void afAPSF_ConfigGet(uint8 endPoint, afAPSF_Config_t *pCfg);

 /*
  *	afAPSF_ConfigSet - set the fragmentation configuration for the specified EndPoint.
  */
afStatus_t afAPSF_ConfigSet(uint8 endPoint, afAPSF_Config_t *pCfg);

 /*
  *	afSetApplCB - Sets the pointer to the Application Callback function for a
  *               specific EndPoint.
  */
uint8 afSetApplCB( uint8 endPoint, pApplCB pApplFn );





/**************************************************************************************************
*/
#line 45 "F:\\Workspace\\zigbfuzz\\depenInfer/zcl.c"

#line 1 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl.h"
/**************************************************************************************************
  Filename:       zcl.h
  Revised:        $Date: 2014-11-25 09:19:55 -0800 (Tue, 25 Nov 2014) $
  Revision:       $Revision: 41240 $

  Description:    This file contains the Zigbee Cluster Library Foundation definitions.


  Copyright 2006-2014 Texas Instruments Incorporated. All rights reserved.

  IMPORTANT: Your use of this Software is limited to those specific rights
  granted under the terms of a software license agreement between the user
  who downloaded the software, his/her employer (which must be your employer)
  and Texas Instruments Incorporated (the "License").  You may not use this
  Software unless you agree to abide by the terms of the License. The License
  limits your use, and you acknowledge, that the Software may not be modified,
  copied or distributed unless embedded on a Texas Instruments microcontroller
  or used solely and exclusively in conjunction with a Texas Instruments radio
  frequency transceiver, which is integrated into your product.  Other than for
  the foregoing purpose, you may not use, reproduce, copy, prepare derivative
  works of, modify, distribute, perform, display or sell this Software and/or
  its documentation for any purpose.

  YOU FURTHER ACKNOWLEDGE AND AGREE THAT THE SOFTWARE AND DOCUMENTATION ARE
  PROVIDED "AS IS" WITHOUT WARRANTY OF ANY KIND, EITHER EXPRESS OR IMPLIED,
  INCLUDING WITHOUT LIMITATION, ANY WARRANTY OF MERCHANTABILITY, TITLE,
  NON-INFRINGEMENT AND FITNESS FOR A PARTICULAR PURPOSE. IN NO EVENT SHALL
  TEXAS INSTRUMENTS OR ITS LICENSORS BE LIABLE OR OBLIGATED UNDER CONTRACT,
  NEGLIGENCE, STRICT LIABILITY, CONTRIBUTION, BREACH OF WARRANTY, OR OTHER
  LEGAL EQUITABLE THEORY ANY DIRECT OR INDIRECT DAMAGES OR EXPENSES
  INCLUDING BUT NOT LIMITED TO ANY INCIDENTAL, SPECIAL, INDIRECT, PUNITIVE
  OR CONSEQUENTIAL DAMAGES, LOST PROFITS OR LOST DATA, COST OF PROCUREMENT
  OF SUBSTITUTE GOODS, TECHNOLOGY, SERVICES, OR ANY CLAIMS BY THIRD PARTIES
  (INCLUDING BUT NOT LIMITED TO ANY DEFENSE THEREOF), OR OTHER SIMILAR COSTS.

  Should you have any questions regarding your right to use this Software,
  contact Texas Instruments Incorporated at www.TI.com.
**************************************************************************************************/















/*********************************************************************
 * INCLUDES
 */
#line 1 "F:\\Workspace\\zstack_iar_zf\\Components\\osal\\include\\OSAL_Nv.h"
/**************************************************************************************************
  Filename:       OSAL_Nv.h
  Revised:        $Date: 2014-10-06 15:40:15 -0700 (Mon, 06 Oct 2014) $
  Revision:       $Revision: 40448 $

  Description:    This module defines the OSAL non-volatile memory functions.


  Copyright 2004-2011 Texas Instruments Incorporated. All rights reserved.

  IMPORTANT: Your use of this Software is limited to those specific rights
  granted under the terms of a software license agreement between the user
  who downloaded the software, his/her employer (which must be your employer)
  and Texas Instruments Incorporated (the "License"). You may not use this
  Software unless you agree to abide by the terms of the License. The License
  limits your use, and you acknowledge, that the Software may not be modified,
  copied or distributed unless embedded on a Texas Instruments microcontroller
  or used solely and exclusively in conjunction with a Texas Instruments radio
  frequency transceiver, which is integrated into your product. Other than for
  the foregoing purpose, you may not use, reproduce, copy, prepare derivative
  works of, modify, distribute, perform, display or sell this Software and/or
  its documentation for any purpose.

  YOU FURTHER ACKNOWLEDGE AND AGREE THAT THE SOFTWARE AND DOCUMENTATION ARE
  PROVIDED “AS IS” WITHOUT WARRANTY OF ANY KIND, EITHER EXPRESS OR IMPLIED,
  INCLUDING WITHOUT LIMITATION, ANY WARRANTY OF MERCHANTABILITY, TITLE,
  NON-INFRINGEMENT AND FITNESS FOR A PARTICULAR PURPOSE. IN NO EVENT SHALL
  TEXAS INSTRUMENTS OR ITS LICENSORS BE LIABLE OR OBLIGATED UNDER CONTRACT,
  NEGLIGENCE, STRICT LIABILITY, CONTRIBUTION, BREACH OF WARRANTY, OR OTHER
  LEGAL EQUITABLE THEORY ANY DIRECT OR INDIRECT DAMAGES OR EXPENSES
  INCLUDING BUT NOT LIMITED TO ANY INCIDENTAL, SPECIAL, INDIRECT, PUNITIVE
  OR CONSEQUENTIAL DAMAGES, LOST PROFITS OR LOST DATA, COST OF PROCUREMENT
  OF SUBSTITUTE GOODS, TECHNOLOGY, SERVICES, OR ANY CLAIMS BY THIRD PARTIES
  (INCLUDING BUT NOT LIMITED TO ANY DEFENSE THEREOF), OR OTHER SIMILAR COSTS.

  Should you have any questions regarding your right to use this Software,
  contact Texas Instruments Incorporated at www.TI.com.
**************************************************************************************************/









/*********************************************************************
 * INCLUDES
 */



/*********************************************************************
 * CONSTANTS
 */

/*********************************************************************
 * MACROS
 */

/*********************************************************************
 * TYPEDEFS
 */

/*********************************************************************
 * GLOBAL VARIABLES
 */

/*********************************************************************
 * FUNCTIONS
 */

/*
 * Initialize NV service
 */
extern void osal_nv_init( void *p );

/*
 * Initialize an item in NV
 */
extern uint8 osal_nv_item_init( uint16 id, uint16 len, void *buf );

/*
 * Read an NV attribute
 */
extern uint8 osal_nv_read( uint16 id, uint16 offset, uint16 len, void *buf );

/*
 * Write an NV attribute
 */
extern uint8 osal_nv_write( uint16 id, uint16 offset, uint16 len, void *buf );

/*
 * Get the length of an NV item.
 */
extern uint16 osal_nv_item_len( uint16 id );

/*
 * Delete an NV item.
 */
extern uint8 osal_nv_delete( uint16 id, uint16 len );

#line 131 "F:\\Workspace\\zstack_iar_zf\\Components\\osal\\include\\OSAL_Nv.h"

/*********************************************************************
*********************************************************************/





#line 60 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl.h"
#line 1 "F:\\Workspace\\zstack_iar_zf\\Components\\osal\\include\\OSAL_Tasks.h"
/**************************************************************************************************
  Filename:       OSAL_Tasks.h
  Revised:        $Date: 2014-06-16 15:12:16 -0700 (Mon, 16 Jun 2014) $
  Revision:       $Revision: 39036 $

  Description:    This file contains the OSAL Task definition and manipulation functions.


  Copyright 2004-2007 Texas Instruments Incorporated. All rights reserved.

  IMPORTANT: Your use of this Software is limited to those specific rights
  granted under the terms of a software license agreement between the user
  who downloaded the software, his/her employer (which must be your employer)
  and Texas Instruments Incorporated (the "License").  You may not use this
  Software unless you agree to abide by the terms of the License. The License
  limits your use, and you acknowledge, that the Software may not be modified,
  copied or distributed unless embedded on a Texas Instruments microcontroller
  or used solely and exclusively in conjunction with a Texas Instruments radio
  frequency transceiver, which is integrated into your product.  Other than for
  the foregoing purpose, you may not use, reproduce, copy, prepare derivative
  works of, modify, distribute, perform, display or sell this Software and/or
  its documentation for any purpose.

  YOU FURTHER ACKNOWLEDGE AND AGREE THAT THE SOFTWARE AND DOCUMENTATION ARE
  PROVIDED “AS IS” WITHOUT WARRANTY OF ANY KIND, EITHER EXPRESS OR IMPLIED, 
  INCLUDING WITHOUT LIMITATION, ANY WARRANTY OF MERCHANTABILITY, TITLE, 
  NON-INFRINGEMENT AND FITNESS FOR A PARTICULAR PURPOSE. IN NO EVENT SHALL
  TEXAS INSTRUMENTS OR ITS LICENSORS BE LIABLE OR OBLIGATED UNDER CONTRACT,
  NEGLIGENCE, STRICT LIABILITY, CONTRIBUTION, BREACH OF WARRANTY, OR OTHER
  LEGAL EQUITABLE THEORY ANY DIRECT OR INDIRECT DAMAGES OR EXPENSES
  INCLUDING BUT NOT LIMITED TO ANY INCIDENTAL, SPECIAL, INDIRECT, PUNITIVE
  OR CONSEQUENTIAL DAMAGES, LOST PROFITS OR LOST DATA, COST OF PROCUREMENT
  OF SUBSTITUTE GOODS, TECHNOLOGY, SERVICES, OR ANY CLAIMS BY THIRD PARTIES
  (INCLUDING BUT NOT LIMITED TO ANY DEFENSE THEREOF), OR OTHER SIMILAR COSTS.

  Should you have any questions regarding your right to use this Software,
  contact Texas Instruments Incorporated at www.TI.com. 
**************************************************************************************************/









/*********************************************************************
 * INCLUDES
 */

/*********************************************************************
 * MACROS
 */

/*********************************************************************
 * CONSTANTS
 */






/*********************************************************************
 * TYPEDEFS
 */

/*
 * Event handler function prototype
 */
typedef unsigned short (*pTaskEventHandlerFn)( unsigned char task_id, unsigned short event );

/*********************************************************************
 * GLOBAL VARIABLES
 */

extern const pTaskEventHandlerFn tasksArr[];
extern const uint8 tasksCnt;
extern uint16 *tasksEvents;

/*********************************************************************
 * FUNCTIONS
 */

/*
 * Call each of the tasks initailization functions.
 */
extern void osalInitTasks( void );

/*********************************************************************
*********************************************************************/





#line 61 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl.h"


#line 1 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\nwk\\aps_groups.h"
/**************************************************************************************************
  Filename:       aps_groups.h
  Revised:        $Date: 2007-10-28 18:41:49 -0700 (Sun, 28 Oct 2007) $
  Revision:       $Revision: 15799 $

  Description:    Application Support Sub Layer group management functions.


  Copyright 2006-2007 Texas Instruments Incorporated. All rights reserved.

  IMPORTANT: Your use of this Software is limited to those specific rights
  granted under the terms of a software license agreement between the user
  who downloaded the software, his/her employer (which must be your employer)
  and Texas Instruments Incorporated (the "License").  You may not use this
  Software unless you agree to abide by the terms of the License. The License
  limits your use, and you acknowledge, that the Software may not be modified,
  copied or distributed unless embedded on a Texas Instruments microcontroller
  or used solely and exclusively in conjunction with a Texas Instruments radio
  frequency transceiver, which is integrated into your product.  Other than for
  the foregoing purpose, you may not use, reproduce, copy, prepare derivative
  works of, modify, distribute, perform, display or sell this Software and/or
  its documentation for any purpose.

  YOU FURTHER ACKNOWLEDGE AND AGREE THAT THE SOFTWARE AND DOCUMENTATION ARE
  PROVIDED “AS IS” WITHOUT WARRANTY OF ANY KIND, EITHER EXPRESS OR IMPLIED, 
  INCLUDING WITHOUT LIMITATION, ANY WARRANTY OF MERCHANTABILITY, TITLE, 
  NON-INFRINGEMENT AND FITNESS FOR A PARTICULAR PURPOSE. IN NO EVENT SHALL
  TEXAS INSTRUMENTS OR ITS LICENSORS BE LIABLE OR OBLIGATED UNDER CONTRACT,
  NEGLIGENCE, STRICT LIABILITY, CONTRIBUTION, BREACH OF WARRANTY, OR OTHER
  LEGAL EQUITABLE THEORY ANY DIRECT OR INDIRECT DAMAGES OR EXPENSES
  INCLUDING BUT NOT LIMITED TO ANY INCIDENTAL, SPECIAL, INDIRECT, PUNITIVE
  OR CONSEQUENTIAL DAMAGES, LOST PROFITS OR LOST DATA, COST OF PROCUREMENT
  OF SUBSTITUTE GOODS, TECHNOLOGY, SERVICES, OR ANY CLAIMS BY THIRD PARTIES
  (INCLUDING BUT NOT LIMITED TO ANY DEFENSE THEREOF), OR OTHER SIMILAR COSTS.

  Should you have any questions regarding your right to use this Software,
  contact Texas Instruments Incorporated at www.TI.com. 
**************************************************************************************************/








/*********************************************************************
 * INCLUDES
 */


/*********************************************************************
 * MACROS
 */

  
/*********************************************************************
 * CONSTANTS
 */




  
/*********************************************************************
 * TYPEDEFS
 */

// Group Table Element
typedef struct
{
  uint16 ID;                       // Unique to this table
  uint8  name[16]; // Human readable name of group
} aps_Group_t;

typedef struct apsGroupItem
{
  struct apsGroupItem  *next;
  uint8                endpoint;
  aps_Group_t          group;
} apsGroupItem_t;

/*********************************************************************
 * GLOBAL VARIABLES
 */
extern apsGroupItem_t *apsGroupTable;

/*********************************************************************
 * FUNCTIONS
 */

/*
 * Add a group for an endpoint
 */
extern ZStatus_t aps_AddGroup( uint8 endpoint, aps_Group_t *group );

/*
 * Find a group with endpoint and groupID
 *  - returns a pointer to the group information, NULL if not found
 */
extern aps_Group_t *aps_FindGroup( uint8 endpoint, uint16 groupID );

/*
 * Find a group for an endpoint
 *  - returns endpoint found, or 0xFF for not found
 */
extern uint8 aps_FindGroupForEndpoint( uint16 groupID, uint8 lastEP );

/*
 * Find all groups for an endpoint
 *  - returns number of groups copied to groupList
 */
extern uint8 aps_FindAllGroupsForEndpoint( uint8 endpoint, uint16 *groupList );

/*
 * Remove a group with endpoint and groupID
 *  - returns TRUE if removed, FALSE if not found
 */
extern uint8 aps_RemoveGroup( uint8 endpoint, uint16 groupID );

/*
 * Remove all groups for endpoint
 */
extern void aps_RemoveAllGroup( uint8 endpoint );

/*
 * Count the number of groups for an endpoint
 */
extern uint8 aps_CountGroups( uint8 endpoint );

/*
 * Count the number of groups
 */
extern uint8 aps_CountAllGroups( void );

/*
 * Initialize the Group Table NV Space
 */
extern uint8 aps_GroupsInitNV( void );

/*
 * Initialize the Group Table NV Space to default (no entries)
 */
extern void aps_GroupsSetDefaultNV( void );

/*
 * Write the group table to NV
 */
extern void aps_GroupsWriteNV( void );

/*
 * Read the group table from NV
 */
extern uint16 aps_GroupsRestoreFromNV( void );

/*********************************************************************
*********************************************************************/







#line 65 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl.h"

/*********************************************************************
 * CONSTANTS
 */


  
// General Clusters
#line 96 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl.h"










// Retail Clusters



   
// Closures Clusters




// HVAC Clusters






// Lighting Clusters



// Measurement and Sensing Clusters
#line 135 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl.h"

// Security and Safety (SS) Clusters




// Protocol Interfaces
#line 165 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl.h"

// Smart Energy (SE) Clusters
#line 178 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl.h"
   

  



   
#line 191 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl.h"

// Light Link cluster


 
/*** Frame Control bit mask ***/





/*** Frame Types ***/



/*** Frame Client/Server Directions ***/



/*** Chipcon Manufacturer Code ***/


/*** Foundation Command IDs ***/
#line 234 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl.h"



// define reporting constant


// define command direction flag masks





/*** Data Types ***/
#line 303 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl.h"

/*** Error Status Codes ***/


// 0x02-0x7D are reserved.
#line 335 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl.h"

// 0xbd-bf are reserved.



// 0xc3-0xff are reserved.


/*** Attribute Access Control - bit masks ***/
#line 352 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl.h"
//NOTE: If no global or client access is define, then server side of the attribute is assumed

// Access Control for client

   
// Access Control as reported OTA via DiscoveryAttributesExtended




// Used by Configure Reporting Command



// Predefined Maximum String Length


// Used by zclReadWriteCB_t callback function






/*********************************************************************
 * MACROS
 */








// Padding needed if buffer has odd number of octects in length


// Check for Cluster IDs
#line 410 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl.h"























/*********************************************************************
 * TYPEDEFS
 */
// zcl_ProcessMessageMSG() return codes
typedef enum
{
  ZCL_PROC_SUCCESS = 0,                 // Message was processed
  ZCL_PROC_INVALID ,                    // Format or parameter was wrong
  ZCL_PROC_EP_NOT_FOUND,                // Endpoint descriptor not found
  ZCL_PROC_NOT_OPERATIONAL,             // Can't respond to this command
  ZCL_PROC_INTERPAN_FOUNDATION_CMD,     // INTER-PAN and Foundation Command (not allowed)
  ZCL_PROC_NOT_SECURE,                  // Security was required but the message is not secure
  ZCL_PROC_MANUFACTURER_SPECIFIC,       // Manufacturer Specific command - not handled
  ZCL_PROC_MANUFACTURER_SPECIFIC_DR,    // Manufacturer Specific command - not handled, but default response sent
  ZCL_PROC_NOT_HANDLED,                 // No default response was sent and the message was not handled
  ZCL_PROC_NOT_HANDLED_DR,              // default response was sent and the message was not handled
} zclProcMsgStatus_t;

// ZCL header - frame control field
typedef struct
{
  unsigned int type:2;
  unsigned int manuSpecific:1;
  unsigned int direction:1;
  unsigned int disableDefaultRsp:1;
  unsigned int reserved:3;
} zclFrameControl_t;

// ZCL header
typedef struct
{
  zclFrameControl_t fc;
  uint16            manuCode;
  uint8             transSeqNum;
  uint8             commandID;
} zclFrameHdr_t;


// Read Attribute Command format
typedef struct
{
  uint8  numAttr;            // number of attributes in the list
  uint16 attrID[];           // supported attributes list - this structure should
                             // be allocated with the appropriate number of attributes.
} zclReadCmd_t;

// Read Attribute Response Status record
typedef struct
{
  uint16 attrID;            // attribute ID
  uint8  status;            // should be ZCL_STATUS_SUCCESS or error
  uint8  dataType;          // attribute data type
  uint8  *data;             // this structure is allocated, so the data is HERE
                            // - the size depends on the attribute data type
} zclReadRspStatus_t;

// Read Attribute Response Command format
typedef struct
{
  uint8              numAttr;     // number of attributes in the list
  zclReadRspStatus_t attrList[];  // attribute status list
} zclReadRspCmd_t;


// Write Attribute record
typedef struct
{
  uint16 attrID;             // attribute ID
  uint8  dataType;           // attribute data type
  uint8  *attrData;          // this structure is allocated, so the data is HERE
                             //  - the size depends on the attribute data type
} zclWriteRec_t;

// Write Attribute Command format
typedef struct
{
  uint8         numAttr;     // number of attribute records in the list
  zclWriteRec_t attrList[];  // attribute records
} zclWriteCmd_t;

// Write Attribute Status record
typedef struct
{
  uint8  status;             // should be ZCL_STATUS_SUCCESS or error
  uint16 attrID;             // attribute ID
} zclWriteRspStatus_t;

// Write Attribute Response Command format
typedef struct
{
  uint8               numAttr;     // number of attribute status in the list
  zclWriteRspStatus_t attrList[];  // attribute status records
} zclWriteRspCmd_t;

// Configure Reporting Command format
typedef struct
{
  uint8  direction;          // to send or receive reports of the attribute
  uint16 attrID;             // attribute ID
  uint8  dataType;           // attribute data type
  uint16 minReportInt;       // minimum reporting interval
  uint16 maxReportInt;       // maximum reporting interval, 0xFFFF=off
  uint16 timeoutPeriod;      // timeout period
  uint8  *reportableChange;  // reportable change (only applicable to analog data type)
                             // - the size depends on the attribute data type
} zclCfgReportRec_t;

typedef struct
{
  uint8             numAttr;    // number of attribute IDs in the list
  zclCfgReportRec_t attrList[]; // attribute ID list
} zclCfgReportCmd_t;

// Attribute Status record
typedef struct
{
  uint8  status;             // should be ZCL_STATUS_SUCCESS or error
  uint8  direction;          // whether attributes are reported or reports of attributes are received
  uint16 attrID;             // attribute ID
} zclCfgReportStatus_t;

// Configure Reporting Response Command format
typedef struct
{
  uint8                numAttr;    // number of attribute status in the list
  zclCfgReportStatus_t attrList[]; // attribute status records
} zclCfgReportRspCmd_t;

// Read Reporting Configuration Command format
typedef struct
{
  uint8  direction; // to send or receive reports of the attribute
  uint16 attrID;    // attribute ID
} zclReadReportCfgRec_t;

typedef struct
{
  uint8                 numAttr;    // number of attributes in the list
  zclReadReportCfgRec_t attrList[]; // attribute ID list
} zclReadReportCfgCmd_t;

// Attribute Reporting Configuration record
typedef struct
{
  uint8  status;             // status field
  uint8  direction;          // to send or receive reports of the attribute
  uint16 attrID;             // attribute ID
  uint8  dataType;           // attribute data type
  uint16 minReportInt;       // minimum reporting interval
  uint16 maxReportInt;       // maximum reporting interval
  uint16 timeoutPeriod;      // timeout period
  uint8  *reportableChange;  // reportable change (only applicable to analog data type)
                             // - the size depends on the attribute data type
} zclReportCfgRspRec_t;

// Read Reporting Configuration Response Command format
typedef struct
{
  uint8                numAttr;    // number of records in the list
  zclReportCfgRspRec_t attrList[]; // attribute reporting configuration list
} zclReadReportCfgRspCmd_t;

// Attribute Report
typedef struct
{
  uint16 attrID;             // atrribute ID
  uint8  dataType;           // attribute data type
  uint8  *attrData;          // this structure is allocated, so the data is HERE
                             // - the size depends on the data type of attrID
} zclReport_t;

// Report Attributes Command format
typedef struct
{
  uint8       numAttr;       // number of reports in the list
  zclReport_t attrList[];    // attribute report list
} zclReportCmd_t;

// Default Response Command format
typedef struct
{
  uint8  commandID;
  uint8  statusCode;
} zclDefaultRspCmd_t;

// Discover Attributes and Attributes Extended Command format
typedef struct
{
  uint16 startAttr;          // specifies the minimum value of the identifier
                             // to begin attribute discovery.
  uint8  maxAttrIDs;         // maximum number of attribute IDs that are to be
                             // returned in the resulting response command.
} zclDiscoverAttrsCmd_t;

// Attribute Report info
typedef struct
{
  uint16 attrID;             // attribute ID
  uint8  dataType;           // attribute data type (see Table 17 in Spec)
} zclDiscoverAttrInfo_t;

// Discover Attributes Response Command format
typedef struct
{
  uint8             discComplete; // whether or not there're more attributes to be discovered
  uint8             numAttr;      // number of attributes in the list
  zclDiscoverAttrInfo_t attrList[];   // supported attributes list
} zclDiscoverAttrsRspCmd_t;

// String Data Type
typedef struct
{
  uint8 strLen;
  uint8 *pStr;
} UTF8String_t;

// Command format for the following:
// Discover Commands Received, Discover Commands Generated
typedef struct
{
  uint8 startCmdID;
  uint8 maxCmdID;
} zclDiscoverCmdsCmd_t;

// Command format for the following:
// Discover Commands Received Response Command, Discover Commands Generated Response
typedef struct
{
  uint8 discComplete;
  uint8 cmdType;    // either ZCL_CMD_DISCOVER_CMDS_GEN or ZCL_CMD_DISCOVER_CMDS_RECEIVED
  uint8 numCmd;     // number of provided commands
  uint8 *pCmdID;    // variable length array
} zclDiscoverCmdsCmdRsp_t;

// Discover Attributes Extended Response Command format
typedef struct
{
  uint16 attrID;
  uint8 attrDataType;
  uint8 attrAccessControl;
} zclExtAttrInfo_t;

typedef struct
{
  uint8 discComplete;
  uint8 numAttr;                  // number of attributes provided
  zclExtAttrInfo_t  aExtAttrInfo[];    // variable length array
} zclDiscoverAttrsExtRsp_t;

/*********************************************************************
 * Plugins
 */

// Incoming ZCL message, this buffer will be allocated, cmd will point to the
// the command record.
typedef struct
{
  afIncomingMSGPacket_t *msg;        // incoming message
  zclFrameHdr_t         hdr;         // ZCL header parsed
  uint8                 *pData;      // pointer to data after header
  uint16                pDataLen;    // length of remaining data
  void                  *attrCmd;    // pointer to the parsed attribute or command
} zclIncoming_t;

// Outgoing ZCL Cluster Specific Commands
typedef struct
{
  zclFrameHdr_t hdr;
  uint16        realClusterID;
  uint16        attrID;
  void          *cmdStruct;
  uint8         cmdLen;
  uint8         *cmdData;
} zclOutgoingCmd_t;

// Incoming ZCL message passed to the Application. This buffer will be
// allocated and attrCmd will point to the command record.
//
// NOTE - the Application must deallocate the message plus attrCmd buffer.
//
typedef struct
{
  osal_event_hdr_t hdr;         // OSAL header
  zclFrameHdr_t    zclHdr;      // ZCL header parsed
  uint16           clusterId;   // Cluster ID
  afAddrType_t     srcAddr;     // Sender's address
  uint8            endPoint;    // destination endpoint
  void             *attrCmd;    // pointer to the parsed attribute or command; must be freed by Application
} zclIncomingMsg_t;

// Function pointer type to handle incoming messages.
//   msg - incoming message
//   logicalClusterID - logical cluster ID
typedef ZStatus_t (*zclInHdlr_t)( zclIncoming_t *pInHdlrMsg );

// Function pointer type to handle incoming write commands.
//   msg - incoming message
//   logicalClusterID - logical cluster ID
//   writeRec - received data to be written
typedef ZStatus_t (*zclInWrtHdlr_t)( zclIncoming_t *msg, uint16 logicalClusterID, zclWriteRec_t *writeRec );

// Command record
typedef struct
{
  uint16   clusterID;
  uint8    cmdID;
  uint8    flag;  // one of CMD_DIR_CLIENT_GENERATED, CMD_DIR_CLIENT_RECEIVED, CMD_DIR_SERVER_GENERATED, CMD_DIR_SERVER_RECEIVED
} zclCommandRec_t;

// Attribute record
typedef struct
{
  uint16  attrId;         // Attribute ID
  uint8   dataType;       // Data Type - defined in AF.h
  uint8   accessControl;  // Read/write - bit field
  void    *dataPtr;       // Pointer to data field
} zclAttribute_t;

typedef struct
{
  uint16          clusterID;    // Real cluster ID
  zclAttribute_t  attr;
} zclAttrRec_t;

// Function pointer type to validate attribute data.
//
//   pAttr - where data to be written
//   pAttrInfo - pointer to attribute info
//
//   return  TRUE if data valid. FALSE, otherwise.
typedef uint8 (*zclValidateAttrData_t)( zclAttrRec_t *pAttr, zclWriteRec_t *pAttrInfo );

// Function pointer type to read/write attribute data.
//
//   clusterId - cluster that attribute belongs to
//   attrId - attribute to be read or written
//   oper - ZCL_OPER_LEN, ZCL_OPER_READ, or ZCL_OPER_WRITE
//   pValue - pointer to attribute (length) value
//   pLen - length of attribute value read
//
//   return  ZCL_STATUS_SUCCESS: Operation successful
//           ZCL Error Status: Operation not successful
typedef ZStatus_t (*zclReadWriteCB_t)( uint16 clusterId, uint16 attrId, uint8 oper,
                                       uint8 *pValue, uint16 *pLen );

// Callback function prototype to authorize a Read or Write operation
//   on a given attribute.
//
//   srcAddr - source Address
//   pAttr - pointer to attribute
//   oper - ZCL_OPER_READ, or ZCL_OPER_WRITE
//
//   return  ZCL_STATUS_SUCCESS: Operation authorized
//           ZCL_STATUS_NOT_AUTHORIZED: Operation not authorized
typedef ZStatus_t (*zclAuthorizeCB_t)( afAddrType_t *srcAddr, zclAttrRec_t *pAttr, uint8 oper );

typedef struct
{
  uint16  clusterID;      // Real cluster ID
  uint8   option;
} zclOptionRec_t;

// Parse received command
typedef struct
{
  uint8  endpoint;
  uint16 dataLen;
  uint8  *pData;
} zclParseCmd_t;

// Attribute record list item
typedef struct zclAttrRecsList
{
  struct zclAttrRecsList *next;
  uint8                  endpoint;      // Used to link it into the endpoint descriptor
  zclReadWriteCB_t       pfnReadWriteCB;// Read or Write attribute value callback function
  zclAuthorizeCB_t       pfnAuthorizeCB;// Authorize Read or Write operation
  uint8                  numAttributes; // Number of the following records
  const zclAttrRec_t     *attrs;        // attribute records
} zclAttrRecsList;

/*********************************************************************
 * GLOBAL VARIABLES
 */
extern uint8 zcl_TaskID;
extern uint8 zcl_SeqNum;  //Not longer used, refer to bdb_getZCLFrameCounter() in bdb_interface.h
extern uint8 zcl_InSeqNum;
extern uint8 zcl_TransID;

/*********************************************************************
 * FUNCTION MACROS
 */

/*
 *  Send a Write Command - ZCL_CMD_WRITE
 *  Use like:
 *      ZStatus_t zcl_SendWrite( uint8 srcEP, afAddrType_t *dstAddr, uint16 realClusterID, zclWriteCmd_t *writeCmd, uint8 direction, uint8 disableDefaultRsp, uint8 seqNum );
 */


/*
 *  Send a Write Undivided Command - ZCL_CMD_WRITE_UNDIVIDED
 *  Use like:
 *      ZStatus_t zcl_SendWriteUndivided( uint8 srcEP, afAddrType_t *dstAddr, uint16 realClusterID, zclWriteCmd_t *writeCmd, uint8 direction, uint8 disableDefaultRsp, uint8 seqNum );
 */


/*
 *  Send a Write No Response Command - ZCL_CMD_WRITE_NO_RSP
 *  Use like:
 *      ZStatus_t zcl_SendWriteNoRsp( uint8 srcEP, afAddrType_t *dstAddr, uint16 realClusterID, zclWriteCmd_t *writeCmd, uint8 direction, uint8 disableDefaultRsp, uint8 seqNum );
 */



#line 871 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl.h"

/*********************************************************************
 * FUNCTIONS
 */

 /*
  * callback function to handle messages externally
  */
extern uint8 zcl_HandleExternal( zclIncoming_t *pInMsg );



 /*
  * Initialization for the task
  */
extern void zcl_Init( byte task_id );



/*
 *  Event Process for the task
 */
extern UINT16 zcl_event_loop( byte task_id, UINT16 events );



/*
 *  Register the Application to receive the unprocessed Foundation command/response messages
 */
extern uint8 zcl_registerForMsg( uint8 taskId );

/*
 *  Register a Task to receive the unprocessed Foundation command/response messages
 *  addressed to a specific End Point
 */
extern uint8 zcl_registerForMsgExt( uint8 taskId, uint8 endPointId  );



/*
 *  Function for Plugins' to register for incoming messages
 */
extern ZStatus_t zcl_registerPlugin( uint16 startLogCluster, uint16 endLogCluster,
                                     zclInHdlr_t pfnIncomingHdlr );

/*
 *  Register Application's Command table
 */
extern ZStatus_t zcl_registerCmdList( uint8 endpoint, const uint8 cmdListSize, const zclCommandRec_t newCmdList[] );

/*
 *  Register Application's Attribute table
 */
extern ZStatus_t zcl_registerAttrList( uint8 endpoint, uint8 numAttr, const zclAttrRec_t attrList[] );

/*
 *  Register Application's Cluster Option table
 */
extern ZStatus_t zcl_registerClusterOptionList( uint8 endpoint, uint8 numOption, zclOptionRec_t optionList[] );

/*
 *  Register Application's attribute data validation callback routine
 */
extern ZStatus_t zcl_registerValidateAttrData( zclValidateAttrData_t pfnValidateAttrData );

/*
 *  Register the application's callback function to read/write attribute data.
 */
extern ZStatus_t zcl_registerReadWriteCB( uint8 endpoint, zclReadWriteCB_t pfnReadWriteCB,
                                          zclAuthorizeCB_t pfnAuthorizeCB );

/*
 *  Process incoming ZCL messages
 */
extern zclProcMsgStatus_t zcl_ProcessMessageMSG( afIncomingMSGPacket_t *pkt );

/*
 *  Function for Sending a Command
 */
extern ZStatus_t zcl_SendCommand( uint8 srcEP, afAddrType_t *dstAddr,
                                  uint16 clusterID, uint8 cmd, uint8 specific, uint8 direction,
                                  uint8 disableDefaultRsp, uint16 manuCode, uint8 seqNum,
                                  uint16 cmdFormatLen, uint8 *cmdFormat );


/*
 *  Function for Reading an Attribute
 */
extern ZStatus_t zcl_SendRead( uint8 srcEP, afAddrType_t *dstAddr,
                               uint16 realClusterID, zclReadCmd_t *readCmd,
                               uint8 direction, uint8 disableDefaultRsp, uint8 seqNum );

/*
 *  Function for sending a Read response command
 */
extern ZStatus_t zcl_SendReadRsp( uint8 srcEP, afAddrType_t *dstAddr,
                                  uint16 realClusterID, zclReadRspCmd_t *readRspCmd,
                                  uint8 direction, uint8 disableDefaultRsp, uint8 seqNum );

/*
 *  Function for reading a local attribute
 */
extern ZStatus_t zcl_ReadAttrData( uint8 endpoint, uint16 clusterId, uint16 attrId,
                                   uint8 *pAttrData, uint16 *pDataLen );




/*
 *  Function for Writing an Attribute
 */
extern ZStatus_t zcl_SendWriteRequest( uint8 srcEP, afAddrType_t *dstAddr,
                                       uint16 realClusterID, zclWriteCmd_t *writeCmd,
                                       uint8 cmd, uint8 direction, uint8 disableDefaultRsp, uint8 seqNum );

/*
 *  Function for sending a Write response command
 */
extern ZStatus_t zcl_SendWriteRsp( uint8 srcEP, afAddrType_t *dstAddr,
                                   uint16 realClusterID, zclWriteRspCmd_t *writeRspCmd,
                                   uint8 direction, uint8 disableDefaultRsp, uint8 seqNum );



/*
 *  Function for Configuring the Reporting mechanism for one or more attributes
 */
extern ZStatus_t zcl_SendConfigReportCmd( uint8 srcEP, afAddrType_t *dstAddr,
                          uint16 realClusterID, zclCfgReportCmd_t *cfgReportCmd,
                          uint8 direction, uint8 disableDefaultRsp, uint8 seqNum );




/*
 *  Function for sending a Configure Reporting Response Command
 */
extern ZStatus_t zcl_SendConfigReportRspCmd( uint8 srcEP, afAddrType_t *dstAddr,
                    uint16 realClusterID, zclCfgReportRspCmd_t *cfgReportRspCmd,
                    uint8 direction, uint8 disableDefaultRsp, uint8 seqNum );



/*
 *  Function for Reading the configuration details of the Reporting mechanism
 */
extern ZStatus_t zcl_SendReadReportCfgCmd( uint8 srcEP, afAddrType_t *dstAddr,
                              uint16 realClusterID, zclReadReportCfgCmd_t *readReportCfgCmd,
                              uint8 direction, uint8 disableDefaultRsp, uint8 seqNum );



/*
 *  Function for sending a Read Reporting Configuration Response command
 */
extern ZStatus_t zcl_SendReadReportCfgRspCmd( uint8 srcEP, afAddrType_t *dstAddr,
                        uint16 realClusterID, zclReadReportCfgRspCmd_t *readReportCfgRspCmd,
                        uint8 direction, uint8 disableDefaultRsp, uint8 seqNum );

/*
 *  Function for Reporting the value of one or more attributes
 */
extern ZStatus_t zcl_SendReportCmd( uint8 srcEP, afAddrType_t *dstAddr,
                              uint16 realClusterID, zclReportCmd_t *reportCmd,
                              uint8 direction, uint8 disableDefaultRsp, uint8 seqNum );


/*
 *  Function for sending the Default Response command
 */
extern ZStatus_t zcl_SendDefaultRspCmd( uint8 srcEP, afAddrType_t *dstAddr, uint16 realClusterID,
                                        zclDefaultRspCmd_t *defaultRspCmd, uint8 direction,
                                        uint8 disableDefaultRsp, uint16 manuCode, uint8 seqNum );


/*
 *  Function to Discover the ID and Types of commands on a remote device
 */
extern ZStatus_t zcl_SendDiscoverCmdsCmd( uint8 srcEP, afAddrType_t *dstAddr,
                            uint16 clusterID, uint8 cmdType, zclDiscoverCmdsCmd_t *pDiscoverCmd,
                            uint8 direction, uint8 disableDefaultRsp, uint8 seqNum );

/*
 *  Function for sending the Discover Commands Response command
 */
extern ZStatus_t zcl_SendDiscoverCmdsRspCmd( uint8 srcEP, afAddrType_t *dstAddr,
                          uint16 clusterID, zclDiscoverCmdsCmdRsp_t *pDiscoverRspCmd,
                          uint8 direction, uint8 disableDefaultRsp, uint8 seqNum );

/*
 *  Function to Discover the ID and Types of the Attributes on a remote device
 */
extern ZStatus_t zcl_SendDiscoverAttrsCmd( uint8 srcEP, afAddrType_t *dstAddr,
                            uint16 realClusterID, zclDiscoverAttrsCmd_t *pDiscoverCmd,
                            uint8 direction, uint8 disableDefaultRsp, uint8 seqNum );

/*
 *  Function for sending the Discover Attributes Response command
 */
extern ZStatus_t zcl_SendDiscoverAttrsRspCmd( uint8 srcEP, afAddrType_t *dstAddr,
                      uint16 realClusterID, zclDiscoverAttrsRspCmd_t *pDiscoverRspCmd,
                      uint8 direction, uint8 disableDefaultRsp, uint8 seqNum );

/*
 * Function for sending the Discover Attributes Extended command
 */
extern ZStatus_t zcl_SendDiscoverAttrsExt( uint8 srcEP, afAddrType_t *dstAddr,
                                     uint16 realClusterID, zclDiscoverAttrsCmd_t *pDiscoverAttrsExt,
                                     uint8 direction, uint8 disableDefaultRsp, uint8 seqNum );

/*
 * Function for sending the Discover Attributes Extended Response command
 */
extern ZStatus_t zcl_SendDiscoverAttrsExtRsp( uint8 srcEP, afAddrType_t *dstAddr,
                                         uint16 realClusterID, zclDiscoverAttrsExtRsp_t *pDiscoverAttrsExtRsp,
                                         uint8 direction, uint8 disableDefaultRsp, uint8 seqNum );



/*
 * Function to parse the "Profile" Read Commands
 */
extern void *zclParseInReadCmd( zclParseCmd_t *pCmd );



/*
 * Function to parse the "Profile" Write, Write Undivided and Write No Response
 * Commands
 */
extern void *zclParseInWriteCmd( zclParseCmd_t *pCmd );



/*
 * Function to parse the "Profile" Configure Reporting Command
 */
extern void *zclParseInConfigReportCmd( zclParseCmd_t *pCmd );
/*
 * Function to parse the "Profile" Read Reporting Configuration Command
 */
extern void *zclParseInReadReportCfgCmd( zclParseCmd_t *pCmd );



/*
 * Function to check to see if Data Type is Analog
 */
extern uint8 zclAnalogDataType( uint8 dataType );




/*
 * Function to parse the "Profile" Report attribute Command
 */
extern void *zclParseInReportCmd( zclParseCmd_t *pCmd );



/*
 * Function to parse the "Profile" Discover Commands Command
 */
extern void *zclParseInDiscCmdsCmd( zclParseCmd_t *pCmd );

/*
 * Function to parse the "Profile" Discover Attributes and Attributes Extended Commands
 */
extern void *zclParseInDiscAttrsCmd( zclParseCmd_t *pCmd );

/*
 * Function to find the command record that matchs the parameters
 */
extern uint8 zclFindCmdRec( uint8 endpoint, uint16 clusterID, uint8 cmdID, zclCommandRec_t *pCmd );


/*
 * Function to parse header of the ZCL format
 */
extern uint8 *zclParseHdr( zclFrameHdr_t *hdr, uint8 *pData );

/*
 * Function to find the attribute record that matchs the parameters
 */
extern uint8 zclFindAttrRec( uint8 endpoint, uint16 realClusterID, uint16 attrId, zclAttrRec_t *pAttr );

#line 1163 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl.h"

/*
 * Function to read the attribute's current value
 */
extern ZStatus_t zclReadAttrData( uint8 *pAttrData, zclAttrRec_t *pAttr, uint16 *pDataLen );

/*
 * Function to return the length of the datatype in length.
 */
extern uint8 zclGetDataTypeLength( uint8 dataType );

/*
 * Function to serialize attribute data.
 */
extern uint8 *zclSerializeData( uint8 dataType, void *attrData, uint8 *buf );

/*
 * Function to return the length of the attribute.
 */
extern uint16 zclGetAttrDataLength( uint8 dataType, uint8 *pData);

/*
 * Call to get original unprocessed AF message (not parsed by ZCL).
 *
 *   NOTE:  This function can only be called during a ZCL callback function
 *          and the calling function must NOT change any data in the message.
 *
 *  returns a pointer to original AF message, NULL if not processing
 *          AF message.
 */
extern afIncomingMSGPacket_t *zcl_getRawAFMsg( void );

/*
 * Call to the get the transaction sequence number from the incoming message.
 *
 *   NOTE:  This function can only be called during a ZCL callback function
 *          and the calling function must NOT change any data in the message.
 *
 * returns the transaction sequence number.
 */
extern uint8 zcl_getParsedTransSeqNum( void );



/*********************************************************************
*********************************************************************/





#line 47 "F:\\Workspace\\zigbfuzz\\depenInfer/zcl.c"
#line 1 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl_general.h"
/**************************************************************************************************
  Filename:       zcl_general.h
  Revised:        $Date: 2014-10-14 13:03:14 -0700 (Tue, 14 Oct 2014) $
  Revision:       $Revision: 40629 $

  Description:    This file contains the ZCL General definitions.


  Copyright 2006-2014 Texas Instruments Incorporated. All rights reserved.

  IMPORTANT: Your use of this Software is limited to those specific rights
  granted under the terms of a software license agreement between the user
  who downloaded the software, his/her employer (which must be your employer)
  and Texas Instruments Incorporated (the "License").  You may not use this
  Software unless you agree to abide by the terms of the License. The License
  limits your use, and you acknowledge, that the Software may not be modified,
  copied or distributed unless embedded on a Texas Instruments microcontroller
  or used solely and exclusively in conjunction with a Texas Instruments radio
  frequency transceiver, which is integrated into your product.  Other than for
  the foregoing purpose, you may not use, reproduce, copy, prepare derivative
  works of, modify, distribute, perform, display or sell this Software and/or
  its documentation for any purpose.

  YOU FURTHER ACKNOWLEDGE AND AGREE THAT THE SOFTWARE AND DOCUMENTATION ARE
  PROVIDED "AS IS" WITHOUT WARRANTY OF ANY KIND, EITHER EXPRESS OR IMPLIED,
  INCLUDING WITHOUT LIMITATION, ANY WARRANTY OF MERCHANTABILITY, TITLE,
  NON-INFRINGEMENT AND FITNESS FOR A PARTICULAR PURPOSE. IN NO EVENT SHALL
  TEXAS INSTRUMENTS OR ITS LICENSORS BE LIABLE OR OBLIGATED UNDER CONTRACT,
  NEGLIGENCE, STRICT LIABILITY, CONTRIBUTION, BREACH OF WARRANTY, OR OTHER
  LEGAL EQUITABLE THEORY ANY DIRECT OR INDIRECT DAMAGES OR EXPENSES
  INCLUDING BUT NOT LIMITED TO ANY INCIDENTAL, SPECIAL, INDIRECT, PUNITIVE
  OR CONSEQUENTIAL DAMAGES, LOST PROFITS OR LOST DATA, COST OF PROCUREMENT
  OF SUBSTITUTE GOODS, TECHNOLOGY, SERVICES, OR ANY CLAIMS BY THIRD PARTIES
  (INCLUDING BUT NOT LIMITED TO ANY DEFENSE THEREOF), OR OTHER SIMILAR COSTS.

  Should you have any questions regarding your right to use this Software,
  contact Texas Instruments Incorporated at www.TI.com.
**************************************************************************************************/









/*********************************************************************
 * INCLUDES
 */


/*********************************************************************
 * CONSTANTS
 */


/********************************/
/*** Basic Cluster Attributes ***/
/********************************/
  // Basic Device Information
#line 72 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl_general.h"

  // Basic Device Settings






/*** Power Source Attribute values ***/
  // Bits b0-b6 represent the primary power source of the device
#line 89 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl_general.h"
  // Bit b7 indicates whether the device has a secondary power source in the
  // form of a battery backup

/*** Power Source Attribute bits  ***/



/*** Application Profile Type Attribute values ***/
#line 106 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl_general.h"

/*** Physical Environment Attribute values ***/



// Specified per Profile 0x01-0x7F


/*** Device Enable Attribute values ***/



/*** Alarm Mask Attribute bits ***/



/******************************/
/*** Basic Cluster Commands ***/
/******************************/


/**********************************************/
/*** Power Configuration Cluster Attributes ***/
/**********************************************/
  // Mains Information



  // Mains Settings





  // Battery Information



  // Battery Information Default Attribute Value


  // Battery Settings
#line 163 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl_general.h"

/*** Mains Alarm Mask Attribute bit ***/




/*** Battery Size Attribute values ***/
#line 178 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl_general.h"

/*** Battery Alarm Mask Attribute bit ***/





/*** Alarm Code Field Enumerations for Battery Alarm values ***/
#line 200 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl_general.h"

/*** Battery Alarm State Attribute bit ***/
#line 215 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl_general.h"

/********************************************/
/*** Power Configuration Cluster Commands ***/
/********************************************/
  // No cluster specific commands

/***********************************************************/
/*** Device Temperature Configuration Cluster Attributes ***/
/***********************************************************/
  // Device Temperature Information





  // Device Temperature Settings






/*** Device Temp Alarm_Mask Attribute bits ***/



/*********************************************************/
/*** Device Temperature Configuration Cluster Commands ***/
/*********************************************************/
  // No cluster specific commands

/***********************************/
/*** Identify Cluster Attributes ***/
/***********************************/



/*** Values of the commissionState Attribute ***/



/*********************************/
/*** Identify Cluster Commands ***/
/*********************************/








/*** Values of 'effect identifier' field of 'trigger effect' command ***/
#line 274 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl_general.h"

/*** Values of 'effect variant' field of 'trigger effect' command ***/


/********************************/
/*** Group Cluster Attributes ***/
/********************************/


/******************************/
/*** Group Cluster Commands ***/
/******************************/
#line 292 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl_general.h"






/*********************************/
/*** Scenes Cluster Attributes ***/
/*********************************/
  // Scene Management Information
#line 308 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl_general.h"

/*******************************/
/*** Scenes Cluster Commands ***/
/*******************************/
#line 322 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl_general.h"

#line 332 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl_general.h"

// command parameter


/*********************************/
/*** On/Off Cluster Attributes ***/
/*********************************/






/*******************************/
/*** On/Off Cluster Commands ***/
/*******************************/
#line 354 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl_general.h"

/*** Values of 'effect identifier' field of 'off with effect' command  ***/



/*** Values of 'effect variant' field of 'off with effect' command ***/
// Effect identifier value = 0x00




// Effect identifier value = 0x01


/****************************************/
/*** On/Off Switch Cluster Attributes ***/
/****************************************/
  // Switch Information


  // Switch Settings



/*** On Off Switch Type attribute values ***/




/*** On Off Switch Actions attribute values ***/




/**************************************/
/*** On/Off Switch Cluster Commands ***/
/**************************************/
  // No cluster specific commands

/****************************************/
/*** Level Control Cluster Attributes ***/
/****************************************/
#line 403 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl_general.h"

  // Level Control Default Attribute Values
#line 412 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl_general.h"






/**************************************/
/*** Level Control Cluster Commands ***/
/**************************************/
#line 429 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl_general.h"

/*** Level Control Move (Mode) Command values ***/



/*** Level Control Step (Mode) Command values ***/



/*********************************/
/*** Alarms Cluster Attributes ***/
/*********************************/
  // Alarm Information


/*******************************/
/*** Alarms Cluster Commands ***/
/*******************************/
  // Client generated commands






  // Server generated commands




/*******************************/
/*** Time Cluster Attributes ***/
/*******************************/
#line 472 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl_general.h"




  /*** DST Shift Range Values ***/



  /*** TimeStatus Attribute bits ***/




/*****************************/
/*** Time Cluster Commands ***/
/*****************************/
  // No cluster specific commands

/***********************************/
/*** RSSI Location Cluster Attributes ***/
/***********************************/
  // Location Information






  // Location Settings
#line 509 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl_general.h"

/*** Location Type attribute bits ***/




/*** Location Method attribute values ***/





/*********************************/
/*** Location Cluster Commands ***/
/*********************************/











/**********************************************************/
/*** Input, Output and Value (Basic) Cluster Attributes ***/
/**********************************************************/
#line 557 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl_general.h"

/**********************************************************/
/*** Appliance Control Cluster Attributes ***/
/**********************************************************/ 





  
/*** StatusFlags attribute bits ***/





/*** Reliability attribute types ***/
#line 585 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl_general.h"

/*** EngineeringUnits attribute values ***/
// Values 0x0000 to 0x00fe are reserved for the list of engineering units with
// corresponding values specified in Clause 21 of the BACnet standard.



// Values 0x0100 to 0xffff are available for proprietary use.

/*** Polarity attribute values ***/



/*** ApplicationType attribute bits ***/
// ApplicationType is subdivided into Group, Type and an Index number.

// Application Group = Bits 24 - 31. An indication of the cluster this
// attribute is part of.


// Application Type = Bits 16 - 23. For Analog clusters, the physical
// quantity that the Present Value attribute of the cluster represents.
// For Binary and Multistate clusters, the application usage domain.


// Application Index = Bits 0 - 15. The specific application usage of
// the cluster


/*** Application Groups ***/
#line 624 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl_general.h"

/*** Application Types ***/

// Analog Input (AI) Types:
//   Group = 0x00.
//   Types = 0x00 - 0x0E.
//   Types 0x0F to 0xFE are reserved, Type = 0xFF indicates other.
#line 646 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl_general.h"

// Analog Output (AO) Types:
//   Group = 0x01.
//   Types = 0x00 - 0x0E.
//   Types 0x0F to 0xFE are reserved, Type = 0xFF indicates other.
#line 666 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl_general.h"

// Analog Value (AV) Types:
//   Group = 0x02.
//   Types = 0x00 - 0x03.
//   Types 0x04 to 0xFE are reserved, Type = 0xFF indicates other.





// Binary Input (BI) Types:
//   Group = 0x03.
//   Types = 0x00 - 0x01.
//   Types 0x02 to 0xFE are reserved, Type = 0xFF indicates other.
//   Present Value = 0 represents False, Off, Normal
//   Present Value = 1 represents True, On, Alarm



// Binary Output (BO) Types:
//   Group = 0x04.
//   Types = 0x00 - 0x01.
//   Types 0x02 to 0xFE are reserved, Type = 0xFF indicates other.
//   Present Value = 0 represents False, Off, Normal
//   Present Value = 1 represents True, On, Alarm



// Binary Value (BV) Types:
//   Group = 0x05.
//   Type = 0x00.
//   Types 0x01 to 0xFE are reserved, Type = 0xFF indicates other.
//   Present Value = 0 represents False, Off, Normal
//   Present Value = 1 represents True, On, Alarm


// Multistate Input (MI) Types:
//   Group = 0x0D.
//   Type = 0x00.
//   Types 0x01 to 0xFE are reserved, Type = 0xFF indicates other.


// Multistate Output (MO) Types:
//   Group = 0x0E.
//   Type = 0x00.
//   Types 0x01 to 0xFE are reserved, Type = 0xFF indicates other.


// Multistate Value (MV) Types:
//   Group = 0x13.
//   Type = 0x00.
//   Types 0x01 to 0xFE are reserved, Type = 0xFF indicates other.


/*** Application Indexes ***/

// Analog Input (AI) Indexes
//   Group = 0x00.

// AI Temperature in degrees C Indexes:
//   Type = 0x00.
//   Indexes = 0x0000 - 0x003C.
//   Indexed 0x003D - 0x01FF are reserved, 0x0200 - 0xFFFE are Vendor
//   defined, Index = 0xFFFF indicates other.


// AI Relative humidity in % Indexes:
//   Type = 0x01.
//   Indexes = 0x0000 - 0x0008.
//   Indexed 0x0009 - 0x01FF are reserved, 0x0200 - 0xFFFE are Vendor
//   defined, Index = 0xFFFF indicates other.


// AI Pressure in Pascal Indexes:
//   Type = 0x02.
//   Indexes = 0x0000 - 0x001E.
//   Indexed 0x001F - 0x01FF are reserved, 0x0200 - 0xFFFE are Vendor
//   defined, Index = 0xFFFF indicates other.


// AI Flow in liters/second Indexes:
//   Type = 0x03.
//   Indexes = 0x0000 - 0x0015.
//   Indexed 0x0016 - 0x01FF are reserved, 0x0200 - 0xFFFE are Vendor
//   defined, Index = 0xFFFF indicates other.


// AI Percentage % Indexes:
//   Type = 0x04.
//   Index = 0x0000.
//   Indexed 0x0001 - 0x01FF are reserved, 0x0200 - 0xFFFE are Vendor
//   defined, Index = 0xFFFF indicates other.


// AI Parts per Million PPM Indexes:
//   Type = 0x05.
//   Indexes = 0x0000 - 0x0001.
//   Indexed 0x0002 - 0x01FF are reserved, 0x0200 - 0xFFFE are Vendor
//   defined, Index = 0xFFFF indicates other.


// AI Rotational Speed in RPM Indexes:
//   Type = 0x06.
//   Indexes = 0x0000 - 0x0007.
//   Indexed 0x0008 - 0x01FF are reserved, 0x0200 - 0xFFFE are Vendor
//   defined, Index = 0xFFFF indicates other.


// AI Current in Amps Indexes:
//   Type = 0x07.
//   Index = 0x0000.
//   Indexed 0x0001 - 0x01FF are reserved, 0x0200 - 0xFFFE are Vendor
//   defined, Index = 0xFFFF indicates other.


// AI Frequency in Hz Indexes:
//   Type = 0x08.
//   Index = 0x0000.
//   Indexed 0x0001 - 0x01FF are reserved, 0x0200 - 0xFFFE are Vendor
//   defined, Index = 0xFFFF indicates other.


// AI Power in Watts Indexes:
//   Type = 0x09.
//   Index = 0x0000.
//   Indexed 0x0001 - 0x01FF are reserved, 0x0200 - 0xFFFE are Vendor
//   defined, Index = 0xFFFF indicates other.


// AI Power in kW Indexes:
//   Type = 0x0A.
//   Indexes = 0x0000 - 0x0001.
//   Indexed 0x0002 - 0x01FF are reserved, 0x0200 - 0xFFFE are Vendor
//   defined, Index = 0xFFFF indicates other.


// AI Energy in kWH Indexes:
//   Type = 0x0B.
//   Index = 0x0000.
//   Indexed 0x0001 - 0x01FF are reserved, 0x0200 - 0xFFFE are Vendor
//   defined, Index = 0xFFFF indicates other.


// AI Count - Unitless Indexes:
//   Type = 0x0C.
//   Index = 0x0000.
//   Indexed 0x0001 - 0x01FF are reserved, 0x0200 - 0xFFFE are Vendor
//   defined, Index = 0xFFFF indicates other.


// AI Enthalpy in KJoules/Kg Indexes:
//   Type = 0x0D.
//   Indexes = 0x0000 - 0x0002.
//   Indexed 0x0003 - 0x01FF are reserved, 0x0200 - 0xFFFE are Vendor
//   defined, Index = 0xFFFF indicates other.


// AI Time in Seconds Indexes:
//   Type = 0x0E.
//   Index = 0x0000.
//   Indexed 0x0001 - 0x01FF are reserved, 0x0200 - 0xFFFE are Vendor
//   defined, Index = 0xFFFF indicates other.



// Analog Output (AO) types
//   Group = 0x01.

// AO Temperature in degrees C Indexes:
//   Type = 0x00.
//   Indexes = 0x0000 - 0x0009.
//   Indexed 0x000A - 0x01FF are reserved, 0x0200 - 0xFFFE are Vendor
//   defined, Index = 0xFFFF indicates other.


// AO Relative Humidity in % Indexes:
//   Type = 0x01.
//   Indexes = 0x0000 - 0x0001.
//   Indexed 0x0002 - 0x01FF are reserved, 0x0200 - 0xFFFE are Vendor
//   defined, Index = 0xFFFF indicates other.


// AO Pressure in Pascal Indexes:
//   Type = 0x02.
//   Indexed 0x0000 - 0x01FF are reserved, 0x0200 - 0xFFFE are Vendor
//   defined, Index = 0xFFFF indicates other.

// AO Flow in liters/second Indexes:
//   Type = 0x03.
//   Indexed 0x0000 - 0x01FF are reserved, 0x0200 - 0xFFFE are Vendor
//   defined, Index = 0xFFFF indicates other.

// AO Percentage % Indexes:
//   Type = 0x04.
//   Indexes = 0x0000 - 0x002D.
//   Indexed 0x002E - 0x01FF are reserved, 0x0200 - 0xFFFE are Vendor
//   defined, Index = 0xFFFF indicates other.


// AO Parts per Million PPM Indexes:
//   Type = 0x05.
//   Index = 0x0000.
//   Indexed 0x0001 - 0x01FF are reserved, 0x0200 - 0xFFFE are Vendor
//   defined, Index = 0xFFFF indicates other.


// AO Rotational Speed in RPM Indexes:
//   Type = 0x06.
//   Indexes = 0x0000 - 0x0004.
//   Indexed 0x0005 - 0x01FF are reserved, 0x0200 - 0xFFFE are Vendor
//   defined, Index = 0xFFFF indicates other.


// AO Current in Amps Indexes:
//   Type = 0x07.
//   Indexed 0x0000 - 0x01FF are reserved, 0x0200 - 0xFFFE are Vendor
//   defined, Index = 0xFFFF indicates other.

// AO Frequency in Hz Indexes:
//   Type = 0x08.
//   Indexed 0x0000 - 0x01FF are reserved, 0x0200 - 0xFFFE are Vendor
//   defined, Index = 0xFFFF indicates other.

// AO Power in Watts Indexes:
//   Type = 0x09.
//   Indexed 0x0000 - 0x01FF are reserved, 0x0200 - 0xFFFE are Vendor
//   defined, Index = 0xFFFF indicates other.

// AO Power in kW Indexes:
//   Type = 0x0A.
//   Indexed 0x0000 - 0x01FF are reserved, 0x0200 - 0xFFFE are Vendor
//   defined, Index = 0xFFFF indicates other.

// AO Energy in kWH Indexes:
//   Type = 0x0B.
//   Indexed 0x0000 - 0x01FF are reserved, 0x0200 - 0xFFFE are Vendor
//   defined, Index = 0xFFFF indicates other.

// AO Count - Unitless Indexes:
//   Type = 0x0C.
//   Indexed 0x0000 - 0x01FF are reserved, 0x0200 - 0xFFFE are Vendor
//   defined, Index = 0xFFFF indicates other.

// AO Enthalpy in KJoules/Kg Indexes:
//   Type = 0x0D.
//   Indexed 0x0000 - 0x01FF are reserved, 0x0200 - 0xFFFE are Vendor
//   defined, Index = 0xFFFF indicates other.

// AO Time in Seconds Indexes:
//   Type = 0x0E.
//   Index = 0x0000.
//   Indexed 0x0001 - 0x01FF are reserved, 0x0200 - 0xFFFE are Vendor
//   defined, Index = 0xFFFF indicates other.



// Analog Value (AV) types
//   Group = 0x02.

// AV Temperature in Degrees C Indexes:
//   Type = 0x00.
//   Indexes = 0x0000 - 0x000F.
//   Indexed 0x0010 - 0x01FF are reserved, 0x0200 - 0xFFFE are Vendor
//   defined, Index = 0xFFFF indicates other.


// AV Area in Square Metres Indexes:
//   Type = 0x01.
//   Index = 0x0000.
//   Indexed 0x0001 - 0x01FF are reserved, 0x0200 - 0xFFFE are Vendor
//   defined, Index = 0xFFFF indicates other.


// AV Multiplier - Number Indexes:
//   Type = 0x02.
//   Index = 0x0000.
//   Indexed 0x0001 - 0x01FF are reserved, 0x0200 - 0xFFFE are Vendor
//   defined, Index = 0xFFFF indicates other.


// AV Flow in Litres/Second Indexes:
//   Type = 0x03.
//   Indexes = 0x0000 - 0x0005.
//   Indexed 0x0006 - 0x01FF are reserved, 0x0200 - 0xFFFE are Vendor
//   defined, Index = 0xFFFF indicates other.



// Binary Input (BI) types
//   Group = 0x03.

// BI Application Domain HVAC Indexes:
//   Type = 0x00.
//   Indexes = 0x0000 - 0x0094.
//   Indexed 0x0095 - 0x01FF are reserved, 0x0200 - 0xFFFE are Vendor
//   defined, Index = 0xFFFF indicates other.


// BI Application Domain Security Indexes:
//   Type = 0x01.
//   Indexes = 0x0000 - 0x0008.
//   Indexed 0x0009 - 0x01FF are reserved, 0x0200 - 0xFFFE are Vendor
//   defined, Index = 0xFFFF indicates other.



// Binary Output (BO) types
//   Group = 0x04.

// BO Application Domain HVAC Indexes:
//   Type = 0x00.
//   Indexes = 0x0000 - 0x0076.
//   Indexed 0x0078 - 0x01FF are reserved, 0x0200 - 0xFFFE are Vendor
//   defined, Index = 0xFFFF indicates other.


// BO Application Domain Security Indexes:
//   Type = 0x02.
//   Indexes = 0x0000 - 0x0003.
//   Indexed 0x0004 - 0x01FF are reserved, 0x0200 - 0xFFFE are Vendor
//   defined, Index = 0xFFFF indicates other.



// Binary Value (BV) types
//   Group = 0x05.

// BV Type Indexes:
//   Type = 0x00.
//   Indexed 0x0000 - 0x01FF are reserved, 0x0200 - 0xFFFE are Vendor
//   defined, Index = 0xFFFF indicates other.

// Multistate Input (MI) types
//   Group = 0x0D.

// MI Application Domain HVAC Indexes:
//   Type = 0x00.
//   Indexes = 0x0000 - 0x000B.
//   Indexed 0x000C - 0x01FF are reserved, 0x0200 - 0xFFFE are Vendor
//   defined, Index = 0xFFFF indicates other.



// Multistate Output (MO)types
//   Group = 0x0E.

// MO Application Domain HVAC Indexes:
//   Type = 0x00.
//   Indexes = 0x0000 - 0x000B.
//   Indexed 0x000C - 0x01FF are reserved, 0x0200 - 0xFFFE are Vendor
//   defined, Index = 0xFFFF indicates other.



// Multistate Value (MV) types
//   Group = 0x13.

// MV Application Domain HVAC Indexes:
//   Type = 0x00.
//   Indexes = 0x0000 - 0x000B.
//   Indexed 0x000C - 0x01FF are reserved, 0x0200 - 0xFFFE are Vendor
//   defined, Index = 0xFFFF indicates other.



// The maximum number of characters to allow in a scene's name
// remember that the first byte is the length


// The maximum length of the scene extension field:
//   2 + 1 + 1 for On/Off cluster (onOff attibute)
//   2 + 1 + 1 for Level Control cluster (currentLevel attribute)
//   2 + 1 + 11 for Color Control cluster (currentX/currentY/EnhancedCurrentHue/CurrentSaturation/colorLoopActive/colorLoopDirection/colorLoopTime attributes)
//   2 + 1 + 1 for Door Lock cluster (Lock State attribute)
//   2 + 1 + 2 for Window Covering cluster (LiftPercentage/TiltPercentage attributes)




// The maximum number of entries in the Scene table




/*********************************************************************
 * TYPEDEFS
 */

// The format of a Scene Table Entry
typedef struct
{
  uint16 groupID;                   // The group ID for which this scene applies
  uint8 ID;                         // Scene ID
  uint16 transTime;                 // Time to take to transition to this scene
  uint16 transTime100ms;            // Together with transTime, this allows transition time to be specified in 1/10s
  uint8 name[16]; // Scene name
  uint8 extLen;                     // Length of extension fields
  uint8 extField[31]; // Extension fields
} zclGeneral_Scene_t;

// The format of an Update Commission State Command Payload
typedef struct
{
  uint8 action;               // describes the action to the CommissionState attr
  uint8 commissionStateMask;  // used by the action parameter to update the CommissionState attr
} zclIdentifyUpdateCommState_t;

// The format of an Alarm Table entry
typedef struct
{
  uint8 code;             // Identifying code for the cause of the alarm
  uint16 clusterID;       // The id of the cluster whose attribute generated this alarm
  uint32 timeStamp;       // The time at which the alarm occured
} zclGeneral_Alarm_t;

// The format of the Get Event Log Command
typedef struct
{
  uint8  logID;     // Log to be queried
  uint32 startTime; // Start time of events
  uint32 endTime;   // End time of events
  uint8  numEvents; // Max number of events requested
} zclGetEventLog_t;

// The format of the Publish Event Log Command Sub Log Payload
typedef struct
{
  uint8  eventId;   // event ID (i.e., associated event configuration attribute ID)
  uint32 eventTime; // UTC time event occured
} zclEventLogPayload_t;

// The format of the Publish Event Log Command
typedef struct
{
  uint8                logID;      // Log to be queried
  uint8                cmdIndex;   // Command index to count payload fragments
  uint8                totalCmds;  // Total number of responses expected
  uint8                numSubLogs; // Number of sub log payloads
  zclEventLogPayload_t *pLogs;     // Sub log payloads (series of events)
} zclPublishEventLog_t;

/*** RSSI Location Cluster Data Types ***/
// Set Absolute Location Command format
typedef struct
{
  int16   coordinate1;
  int16   coordinate2;
  int16   coordinate3;
  int16   power;
  uint16  pathLossExponent;
} zclLocationAbsolute_t;

// Set Device Configuration Command format
typedef struct
{
  int16   power;
  uint16  pathLossExponent;
  uint16  calcPeriod;
  uint8   numMeasurements;
  uint16  reportPeriod;
} zclLocationDevCfg_t;

// Get Location Data Command format
typedef struct
{
  unsigned int absOnly:1;       // Absolute Only
  unsigned int recalc:1;        // Re-calculate
  unsigned int brdcastIndic:1;  // Broadcast Indicator
  unsigned int brdcastRsp:1;    // Broadcast Response
  unsigned int compactRsp:1;    // Compact Response
  unsigned int reserved:3;      // Reserved for future use
} locationbits_t;

typedef union
{
  locationbits_t  locBits;
  uint8           locByte;
} location_t;

typedef struct
{
  location_t   bitmap;
  uint8        numResponses;
  uint8        targetAddr[8];
  // shorthand access





} zclLocationGetData_t;

// Device Configuration Response Command format
typedef struct
{
  uint8               status;
  zclLocationDevCfg_t data;
} zclLocationDevCfgRsp_t;

// Calculated Location Data type
typedef struct
{
  uint8   locationMethod;
  uint8   qualityMeasure;
  uint16  locationAge;
} zclLocationCalculated_t;

// Location Data Type
typedef struct
{
  uint8                    type;
  zclLocationAbsolute_t    absLoc;
  zclLocationCalculated_t  calcLoc;
} zclLocationData_t;

// Location Data Response Command format
typedef struct
{
  uint8              status;
  zclLocationData_t  data;
} zclLocationDataRsp_t;

/*** Structures used for callback functions ***/
typedef struct
{
  afAddrType_t *srcAddr;     // requestor's address
  uint16       identifyTime; // number of seconds the device will continue to identify itself
} zclIdentify_t;

typedef struct
{
  afAddrType_t *srcAddr; // requestor's address
  uint8        effectId;      // identify effect to use
  uint8        effectVariant; // which variant of effect to be triggered
} zclIdentifyTriggerEffect_t;

typedef struct
{
  afAddrType_t *srcAddr; // requestor's address
  uint16       timeout;  // number of seconds the device will continue to identify itself
} zclIdentifyQueryRsp_t;

typedef struct
{
  afAddrType_t *srcAddr;      // requestor's address
  uint8        effectId;      // identify effect to use
  uint8        effectVariant; // which variant of effect to be triggered
} zclOffWithEffect_t;

typedef struct
{
  unsigned int acceptOnlyWhenOn:1;
  unsigned int reserved:7;
} zclOnOffCtrlBits_t;

typedef union
{
  zclOnOffCtrlBits_t bits;
  uint8 byte;
} zclOnOffCtrl_t;

typedef struct
{
  zclOnOffCtrl_t onOffCtrl;    // how the lamp is to be operated
  uint16         onTime;      // the length of time (in 1/10ths second) that the lamp is to remain on, before automatically turning off
  uint16         offWaitTime; // the length of time (in 1/10ths second) that the lamp shall remain off, and guarded to prevent an on command turning the light back on.
} zclOnWithTimedOff_t;

typedef struct
{
  uint8  level;          // new level to move to
  uint16 transitionTime; // time to take to move to the new level (in seconds)
  uint8  withOnOff;      // with On/off command
} zclLCMoveToLevel_t;

typedef struct
{
  uint8 moveMode;  // move mode which is either LEVEL_MOVE_STOP, LEVEL_MOVE_UP,
                   // LEVEL_MOVE_ON_AND_UP, LEVEL_MOVE_DOWN, or LEVEL_MOVE_DOWN_AND_OFF
  uint8 rate;      // rate of movement in steps per second
  uint8 withOnOff; // with On/off command
} zclLCMove_t;

typedef struct
{
  uint8  stepMode;       // step mode which is either LEVEL_STEP_UP, LEVEL_STEP_ON_AND_UP,
                         // LEVEL_STEP_DOWN, or LEVEL_STEP_DOWN_AND_OFF
  uint8  amount;         // number of levels to step
  uint16 transitionTime; // time, in 1/10ths of a second, to take to perform the step
  uint8  withOnOff;      // with On/off command
} zclLCStep_t;

typedef struct
{
  afAddrType_t *srcAddr; // requestor's address
  uint8        cmdID;    // which group message - COMMAND_GROUP_ADD_RSP, COMMAND_GROUP_VIEW_RSP,
                         // COMMAND_GROUP_REMOVE_RSP or COMMAND_GROUP_GET_MEMBERSHIP_RSP
  uint8        status;   // GROUP_STATUS_SUCCESS, GROUP_STATUS_TABLE_FULL,
                         // GROUP_STATUS_ALREADY_IN_TABLE, or GROUP_STATUS_NOT_IN_TABLE. Not
                         // valid for COMMAND_GROUP_GET_MEMBERSHIP_RSP
  uint8        grpCnt;   // number of groups contained in group list
  uint16       *grpList; // what group IDs the action was performed on
  uint8        capacity; // remaining capacity of group table
  uint8        *grpName; // only valid for COMMAND_GROUP_VIEW_RSP
} zclGroupRsp_t;

typedef struct
{
   afAddrType_t       *srcAddr; // requestor's address
   zclGeneral_Scene_t *scene;   // pointer to the scene structure
} zclSceneReq_t;

typedef struct
{
  afAddrType_t       *srcAddr;   // requestor's address
  uint8              cmdID;      // which response - COMMAND_SCENE_ADD_RSP, COMMAND_SCENE_VIEW_RSP,
                                 // COMMAND_SCENE_REMOVE_RSP, COMMAND_SCENE_REMOVE_ALL_RSP,
                                 // COMMAND_SCENE_STORE_RSP or COMMAND_SCENE_GET_MEMBERSHIPSHIP_RSP
  uint8              status;     // response status
  uint8              sceneCnt;   // number of scenes in the scene list (only valid for
                                 // COMMAND_SCENE_GET_MEMBERSHIPSHIP_RSP)
  uint8              *sceneList; // list of scene IDs (only valid for COMMAND_SCENE_GET_MEMBERSHIPSHIP_RSP)
  uint8              capacity;   // remaining capacity of the scene table (only valid for
                                 // COMMAND_SCENE_GET_MEMBERSHIPSHIP_RSP)
  zclGeneral_Scene_t *scene;     // pointer to the scene structure
} zclSceneRsp_t;

typedef struct
{
  afAddrType_t *srcAddr;  // requestor's address
  uint8        cmdID;     // COMMAND_ALARMS_ALARM or COMMAND_ALARMS_GET_RSP
  uint8        status;    // response status (only applicable to COMMAND_ALARMS_GET_RSP)
  uint8        alarmCode; // response status (only applicable to COMMAND_ALARMS_GET_RSP)
  uint16       clusterID; // the id of the cluster whose attribute generated this alarm
  uint32       timeStamp; // the time at which the alarm occurred (only applicable to
                          // COMMAND_ALARMS_GET_RSP)
} zclAlarm_t;

typedef struct
{
  afAddrType_t            *srcAddr;  // requestor's address
  uint8                   cmdID;     // COMMAND_LOCATION_SET_ABSOLUTE, COMMAND_LOCATION_SET_DEV_CFG,
                                     // COMMAND_LOCATION_GET_DEV_CFG or COMMAND_LOCATION_GET_DATA
  union
  {
    zclLocationAbsolute_t absLoc;    // Absolute Location info (only valid for COMMAND_LOCATION_SET_ABSOLUTE)
    zclLocationGetData_t  loc;       // Get Location info (only valid for COMMAND_LOCATION_GET_DATA)
    zclLocationDevCfg_t   devCfg;    // Device Config info (only valid for COMMAND_LOCATION_SET_DEV_CFG)
    uint8                 *ieeeAddr; // Device's IEEE Addr (only valid for COMMAND_LOCATION_GET_DEV_CFG)
  } un;
  uint8                   seqNum;    // Sequence number received with the message  (only valid for GET commands)
} zclLocation_t;

typedef struct
{
  afAddrType_t             *srcAddr;     // requestor's address
  uint8                    cmdID;        // COMMAND_LOCATION_DEV_CFG_RSP, COMMAND_LOCATION_DATA_RSP,
                                         // COMMAND_LOCATION_DATA_NOTIF, COMMAND_LOCATION_COMPACT_DATA_NOTIF
                                         // or COMMAND_LOCATION_RSSI_PING
  union
  {
    zclLocationDataRsp_t   loc;          // the Location Data Response command (applicable to Data Response/Notification)
    zclLocationDevCfgRsp_t devCfg;       // the Device Configuration Response command (only applicable to
                                         // COMMAND_LOCATION_DEV_CFG_RSP)
    uint8                  locationType; // location type (only applicable to COMMAND_LOCATION_RSSI_PING)
  } un;
} zclLocationRsp_t;

// This callback is called to process an incoming Reset to Factory Defaults
// command. On receipt of this command, the device resets all the attributes
// of all its clusters to their factory defaults.
typedef void (*zclGCB_BasicReset_t)( void );

// This callback is called to process an incoming Identify command.
typedef void (*zclGCB_Identify_t)( zclIdentify_t *pCmd );

// This callback is called to process an incoming Identify Trigger Effect command.
typedef void (*zclGCB_IdentifyTriggerEffect_t)( zclIdentifyTriggerEffect_t *pCmd );

// This callback is called to process an incoming Identify EZ-Mode Invoke command.
typedef ZStatus_t (*zclGCB_IdentifyEZModeInvoke_t)( uint8 action );

// This callback is called to process an incoming Identify Update Commission State command.
typedef ZStatus_t (*zclGCB_IdentifyUpdateCommState_t)( zclIdentifyUpdateCommState_t *pCmd );

// This callback is called to process an incoming Identify Query Response command.
typedef void (*zclGCB_IdentifyQueryRsp_t)( zclIdentifyQueryRsp_t *pRsp );

// This callback is called to process an incoming On, Off or Toggle command.
typedef void (*zclGCB_OnOff_t)( uint8 cmd );

// This callback is called to process an incoming Off with Effect
typedef void (*zclGCB_OnOff_OffWithEffect_t)( zclOffWithEffect_t *pCmd );

// This callback is called to process an incoming On with Recall Global Scene command.
typedef void (*zclGCB_OnOff_OnWithRecallGlobalScene_t)( void );

// This callback is called to process an incoming On with Timed Off.
typedef void (*zclGCB_OnOff_OnWithTimedOff_t)( zclOnWithTimedOff_t *pCmd );

// This callback is called to process a Level Control - Move to Level command
typedef void (*zclGCB_LevelControlMoveToLevel_t)( zclLCMoveToLevel_t *pCmd );

// This callback is called to process a Level Control - Move command
typedef void (*zclGCB_LevelControlMove_t)( zclLCMove_t *pCmd );

// This callback is called to process a Level Control - Step command
typedef void (*zclGCB_LevelControlStep_t)( zclLCStep_t *pCmd );

// This callback is called to process a Level Control - Stop command
typedef void (*zclGCB_LevelControlStop_t)( void );

// This callback is called to process an received Group Response message.
// This means that this app sent the request message.
typedef void (*zclGCB_GroupRsp_t)( zclGroupRsp_t *pRsp );

// This callback is called to process an incoming Scene Store request.
// The app will fill in the "extField" with what is needed to restore its
// current settings.
typedef uint8 (*zclGCB_SceneStoreReq_t)( zclSceneReq_t *pReq );

// This callback is called to process an incoming Scene Recall request
// The app will use what's in the "extField" to restore to these settings.
typedef void (*zclGCB_SceneRecallReq_t)( zclSceneReq_t *pReq );

// This callback is called to process an incoming Scene responses. This means
// that this app sent the request for this response.
typedef void (*zclGCB_SceneRsp_t)( zclSceneRsp_t *pRsp );

// This callback is called to process an incoming Alarm request or response command.
typedef void (*zclGCB_Alarm_t)( uint8 direction, zclAlarm_t *pAlarm );

// This callback is called to process an incoming Alarm Get Event Log command.
typedef void (*zclGCB_GetEventLog_t)( uint8 srcEP, afAddrType_t *srcAddr,
                                      zclGetEventLog_t *pEventLog, uint8 seqNum );

// This callback is called to process an incoming Alarm Publish Event Log command.
typedef void (*zclGCB_PublishEventLog_t)( afAddrType_t *srcAddr, zclPublishEventLog_t *pEventLog );

// This callback is called to to process an incoming RSSI Location command.
typedef void (*zclGCB_Location_t)( zclLocation_t *pCmd );

// This callback is called to process an incoming RSSI Location response command.
// This means  that this app sent the request for this response.
typedef void (*zclGCB_LocationRsp_t)( zclLocationRsp_t *pRsp );

// Register Callbacks table entry - enter function pointers for callbacks that
// the application would like to receive
typedef struct
{
  zclGCB_BasicReset_t               pfnBasicReset;                // Basic Cluster Reset command
  zclGCB_IdentifyTriggerEffect_t    pfnIdentifyTriggerEffect;     // Identify Trigger Effect command
  zclGCB_OnOff_t                    pfnOnOff;                     // On/Off cluster commands
  zclGCB_OnOff_OffWithEffect_t      pfnOnOff_OffWithEffect;       // On/Off cluster enhanced command Off with Effect
  zclGCB_OnOff_OnWithRecallGlobalScene_t  pfnOnOff_OnWithRecallGlobalScene;  // On/Off cluster enhanced command On with Recall Global Scene
  zclGCB_OnOff_OnWithTimedOff_t     pfnOnOff_OnWithTimedOff;      // On/Off cluster enhanced command On with Timed Off
#line 1443 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl_general.h"
  zclGCB_Location_t                 pfnLocation;                  // RSSI Location command
  zclGCB_LocationRsp_t              pfnLocationRsp;               // RSSI Location Response command
} zclGeneral_AppCallbacks_t;

/*********************************************************************
 * FUNCTION MACROS
 */

/*
 *  Send a Reset to Factory Defaults Command - COMMAND_BASIC_RESET_FACTORY_DEFAULTS
 *  Use like:
 *      ZStatus_t zclGeneral_SendBasicResetFactoryDefaults( uint16 srcEP, afAddrType_t *dstAddr, uint8 disableDefaultRsp, uint8 seqNum );
 */




/*
 * Send a Identify Query command
 *  Use like:
 *      ZStatus_t zclGeneral_SendIdentifyQuery( uint8 srcEP, afAddrType_t *dstAddr, uint8 disableDefaultRsp, uint8 seqNum );
 */



#line 1532 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl_general.h"

#line 1648 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl_general.h"

#line 1687 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl_general.h"

#line 1747 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl_general.h"

#line 1771 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl_general.h"

#line 1801 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl_general.h"

/*********************************************************************
 * FUNCTIONS
 */

/*
 * Register for callbacks from this cluster library
 */
extern ZStatus_t zclGeneral_RegisterCmdCallbacks( uint8 endpoint, zclGeneral_AppCallbacks_t *callbacks );

#line 1831 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl_general.h"

#line 1875 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl_general.h"

#line 1900 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl_general.h"

#line 2005 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl_general.h"

#line 2024 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl_general.h"


/*
 * Send a Identify message
 */
extern ZStatus_t zclGeneral_SendIdentify( uint8 srcEP, afAddrType_t *dstAddr,
                                          uint16 identifyTime, uint8 disableDefaultRsp, uint8 seqNum );

/*
 * Send an Identify EZ-Mode Invoke message
 */
extern ZStatus_t zclGeneral_SendIdentifyEZModeInvoke( uint8 srcEP, afAddrType_t *dstAddr,
                                                      uint8 action, uint8 disableDefaultRsp, uint8 seqNum );

/*
 * Send an Identify Update Commission State message
 */
extern ZStatus_t zclGeneral_SendIdentifyUpdateCommState( uint8 srcEP, afAddrType_t *dstAddr,
                                                         uint8 action, uint8 commissionStateMask,
                                                         uint8 disableDefaultRsp, uint8 seqNum );

#line 2053 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl_general.h"
/*
 * Send a Identify Query Response message
 */
extern ZStatus_t zclGeneral_SendIdentifyQueryResponse( uint8 srcEP, afAddrType_t *dstAddr,
                                                       uint16 timeout, uint8 disableDefaultRsp, uint8 seqNum );


#line 2094 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl_general.h"

#line 2138 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl_general.h"

#line 2165 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl_general.h"

/*********************************************************************
*********************************************************************/





#line 48 "F:\\Workspace\\zigbfuzz\\depenInfer/zcl.c"




   
#line 1 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\bdb\\bdb_interface.h"
/**************************************************************************************************
  Filename:       bdb_interface.h
  Revised:        $Date: 2016-02-25 11:51:49 -0700 (Thu, 25 Feb 2016) $
  Revision:       $Revision: - $

  Description:    This file contains the Base Device Behavior interface such as 
                  MACRO configuration and API.


  Copyright 2006-2014 Texas Instruments Incorporated. All rights reserved.

  IMPORTANT: Your use of this Software is limited to those specific rights
  granted under the terms of a software license agreement between the user
  who downloaded the software, his/her employer (which must be your employer)
  and Texas Instruments Incorporated (the "License").  You may not use this
  Software unless you agree to abide by the terms of the License. The License
  limits your use, and you acknowledge, that the Software may not be modified,
  copied or distributed unless embedded on a Texas Instruments microcontroller
  or used solely and exclusively in conjunction with a Texas Instruments radio
  frequency transceiver, which is integrated into your product.  Other than for
  the foregoing purpose, you may not use, reproduce, copy, prepare derivative
  works of, modify, distribute, perform, display or sell this Software and/or
  its documentation for any purpose.

  YOU FURTHER ACKNOWLEDGE AND AGREE THAT THE SOFTWARE AND DOCUMENTATION ARE
  PROVIDED "AS IS" WITHOUT WARRANTY OF ANY KIND, EITHER EXPRESS OR IMPLIED,
  INCLUDING WITHOUT LIMITATION, ANY WARRANTY OF MERCHANTABILITY, TITLE,
  NON-INFRINGEMENT AND FITNESS FOR A PARTICULAR PURPOSE. IN NO EVENT SHALL
  TEXAS INSTRUMENTS OR ITS LICENSORS BE LIABLE OR OBLIGATED UNDER CONTRACT,
  NEGLIGENCE, STRICT LIABILITY, CONTRIBUTION, BREACH OF WARRANTY, OR OTHER
  LEGAL EQUITABLE THEORY ANY DIRECT OR INDIRECT DAMAGES OR EXPENSES
  INCLUDING BUT NOT LIMITED TO ANY INCIDENTAL, SPECIAL, INDIRECT, PUNITIVE
  OR CONSEQUENTIAL DAMAGES, LOST PROFITS OR LOST DATA, COST OF PROCUREMENT
  OF SUBSTITUTE GOODS, TECHNOLOGY, SERVICES, OR ANY CLAIMS BY THIRD PARTIES
  (INCLUDING BUT NOT LIMITED TO ANY DEFENSE THEREOF), OR OTHER SIMILAR COSTS.

  Should you have any questions regarding your right to use this Software,
  contact Texas Instruments Incorporated at www.TI.com.
**************************************************************************************************/









/*********************************************************************
 * INCLUDES
 */
#line 1 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\bdb\\bdb.h"
/**************************************************************************************************
  Filename:       bdb.h
  Revised:        $Date: 2016-02-25 11:51:49 -0700 (Thu, 25 Feb 2016) $
  Revision:       $Revision: - $

  Description:    This file contains the Base Device Behavior definitions.


  Copyright 2006-2014 Texas Instruments Incorporated. All rights reserved.

  IMPORTANT: Your use of this Software is limited to those specific rights
  granted under the terms of a software license agreement between the user
  who downloaded the software, his/her employer (which must be your employer)
  and Texas Instruments Incorporated (the "License").  You may not use this
  Software unless you agree to abide by the terms of the License. The License
  limits your use, and you acknowledge, that the Software may not be modified,
  copied or distributed unless embedded on a Texas Instruments microcontroller
  or used solely and exclusively in conjunction with a Texas Instruments radio
  frequency transceiver, which is integrated into your product.  Other than for
  the foregoing purpose, you may not use, reproduce, copy, prepare derivative
  works of, modify, distribute, perform, display or sell this Software and/or
  its documentation for any purpose.

  YOU FURTHER ACKNOWLEDGE AND AGREE THAT THE SOFTWARE AND DOCUMENTATION ARE
  PROVIDED "AS IS" WITHOUT WARRANTY OF ANY KIND, EITHER EXPRESS OR IMPLIED,
  INCLUDING WITHOUT LIMITATION, ANY WARRANTY OF MERCHANTABILITY, TITLE,
  NON-INFRINGEMENT AND FITNESS FOR A PARTICULAR PURPOSE. IN NO EVENT SHALL
  TEXAS INSTRUMENTS OR ITS LICENSORS BE LIABLE OR OBLIGATED UNDER CONTRACT,
  NEGLIGENCE, STRICT LIABILITY, CONTRIBUTION, BREACH OF WARRANTY, OR OTHER
  LEGAL EQUITABLE THEORY ANY DIRECT OR INDIRECT DAMAGES OR EXPENSES
  INCLUDING BUT NOT LIMITED TO ANY INCIDENTAL, SPECIAL, INDIRECT, PUNITIVE
  OR CONSEQUENTIAL DAMAGES, LOST PROFITS OR LOST DATA, COST OF PROCUREMENT
  OF SUBSTITUTE GOODS, TECHNOLOGY, SERVICES, OR ANY CLAIMS BY THIRD PARTIES
  (INCLUDING BUT NOT LIMITED TO ANY DEFENSE THEREOF), OR OTHER SIMILAR COSTS.

  Should you have any questions regarding your right to use this Software,
  contact Texas Instruments Incorporated at www.TI.com.
**************************************************************************************************/









  
  
  
/*********************************************************************
 * INCLUDES
 */
#line 1 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zdo\\ZDProfile.h"
/**************************************************************************************************
  Filename:       ZDProfile.h
  Revised:        $Date: 2015-02-10 15:42:13 -0800 (Tue, 10 Feb 2015) $
  Revision:       $Revision: 42485 $

  Description:    This file contains the interface to the Zigbee Device Object.


  Copyright 2004-2015 Texas Instruments Incorporated. All rights reserved.

  IMPORTANT: Your use of this Software is limited to those specific rights
  granted under the terms of a software license agreement between the user
  who downloaded the software, his/her employer (which must be your employer)
  and Texas Instruments Incorporated (the "License").  You may not use this
  Software unless you agree to abide by the terms of the License. The License
  limits your use, and you acknowledge, that the Software may not be modified,
  copied or distributed unless embedded on a Texas Instruments microcontroller
  or used solely and exclusively in conjunction with a Texas Instruments radio
  frequency transceiver, which is integrated into your product.  Other than for
  the foregoing purpose, you may not use, reproduce, copy, prepare derivative
  works of, modify, distribute, perform, display or sell this Software and/or
  its documentation for any purpose.

  YOU FURTHER ACKNOWLEDGE AND AGREE THAT THE SOFTWARE AND DOCUMENTATION ARE
  PROVIDED “AS IS” WITHOUT WARRANTY OF ANY KIND, EITHER EXPRESS OR IMPLIED,
  INCLUDING WITHOUT LIMITATION, ANY WARRANTY OF MERCHANTABILITY, TITLE,
  NON-INFRINGEMENT AND FITNESS FOR A PARTICULAR PURPOSE. IN NO EVENT SHALL
  TEXAS INSTRUMENTS OR ITS LICENSORS BE LIABLE OR OBLIGATED UNDER CONTRACT,
  NEGLIGENCE, STRICT LIABILITY, CONTRIBUTION, BREACH OF WARRANTY, OR OTHER
  LEGAL EQUITABLE THEORY ANY DIRECT OR INDIRECT DAMAGES OR EXPENSES
  INCLUDING BUT NOT LIMITED TO ANY INCIDENTAL, SPECIAL, INDIRECT, PUNITIVE
  OR CONSEQUENTIAL DAMAGES, LOST PROFITS OR LOST DATA, COST OF PROCUREMENT
  OF SUBSTITUTE GOODS, TECHNOLOGY, SERVICES, OR ANY CLAIMS BY THIRD PARTIES
  (INCLUDING BUT NOT LIMITED TO ANY DEFENSE THEREOF), OR OTHER SIMILAR COSTS.

  Should you have any questions regarding your right to use this Software,
  contact Texas Instruments Incorporated at www.TI.com.
**************************************************************************************************/









/*********************************************************************
 * INCLUDES
 */
#line 1 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zdo\\ZDConfig.h"
/**************************************************************************************************
  Filename:       ZDConfig.h
  Revised:        $Date: 2015-05-18 16:50:53 -0700 (Mon, 18 May 2015) $
  Revision:       $Revision: 43840 $

  Description:    This file contains the configuration attributes for the Zigbee Device Object.
                  These are references to Configuration items that MUST be defined in ZDApp.c.
                  The names mustn't change.


  Copyright 2004-2014 Texas Instruments Incorporated. All rights reserved.

  IMPORTANT: Your use of this Software is limited to those specific rights
  granted under the terms of a software license agreement between the user
  who downloaded the software, his/her employer (which must be your employer)
  and Texas Instruments Incorporated (the "License").  You may not use this
  Software unless you agree to abide by the terms of the License. The License
  limits your use, and you acknowledge, that the Software may not be modified,
  copied or distributed unless embedded on a Texas Instruments microcontroller
  or used solely and exclusively in conjunction with a Texas Instruments radio
  frequency transceiver, which is integrated into your product.  Other than for
  the foregoing purpose, you may not use, reproduce, copy, prepare derivative
  works of, modify, distribute, perform, display or sell this Software and/or
  its documentation for any purpose.

  YOU FURTHER ACKNOWLEDGE AND AGREE THAT THE SOFTWARE AND DOCUMENTATION ARE
  PROVIDED “AS IS” WITHOUT WARRANTY OF ANY KIND, EITHER EXPRESS OR IMPLIED,
  INCLUDING WITHOUT LIMITATION, ANY WARRANTY OF MERCHANTABILITY, TITLE,
  NON-INFRINGEMENT AND FITNESS FOR A PARTICULAR PURPOSE. IN NO EVENT SHALL
  TEXAS INSTRUMENTS OR ITS LICENSORS BE LIABLE OR OBLIGATED UNDER CONTRACT,
  NEGLIGENCE, STRICT LIABILITY, CONTRIBUTION, BREACH OF WARRANTY, OR OTHER
  LEGAL EQUITABLE THEORY ANY DIRECT OR INDIRECT DAMAGES OR EXPENSES
  INCLUDING BUT NOT LIMITED TO ANY INCIDENTAL, SPECIAL, INDIRECT, PUNITIVE
  OR CONSEQUENTIAL DAMAGES, LOST PROFITS OR LOST DATA, COST OF PROCUREMENT
  OF SUBSTITUTE GOODS, TECHNOLOGY, SERVICES, OR ANY CLAIMS BY THIRD PARTIES
  (INCLUDING BUT NOT LIMITED TO ANY DEFENSE THEREOF), OR OTHER SIMILAR COSTS.

  Should you have any questions regarding your right to use this Software,
  contact Texas Instruments Incorporated at www.TI.com.
**************************************************************************************************/









/*********************************************************************
 * INCLUDES
 */
#line 1 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\bdb\\bdb.h"
/**************************************************************************************************
  Filename:       bdb.h
  Revised:        $Date: 2016-02-25 11:51:49 -0700 (Thu, 25 Feb 2016) $
  Revision:       $Revision: - $

  Description:    This file contains the Base Device Behavior definitions.


  Copyright 2006-2014 Texas Instruments Incorporated. All rights reserved.

  IMPORTANT: Your use of this Software is limited to those specific rights
  granted under the terms of a software license agreement between the user
  who downloaded the software, his/her employer (which must be your employer)
  and Texas Instruments Incorporated (the "License").  You may not use this
  Software unless you agree to abide by the terms of the License. The License
  limits your use, and you acknowledge, that the Software may not be modified,
  copied or distributed unless embedded on a Texas Instruments microcontroller
  or used solely and exclusively in conjunction with a Texas Instruments radio
  frequency transceiver, which is integrated into your product.  Other than for
  the foregoing purpose, you may not use, reproduce, copy, prepare derivative
  works of, modify, distribute, perform, display or sell this Software and/or
  its documentation for any purpose.

  YOU FURTHER ACKNOWLEDGE AND AGREE THAT THE SOFTWARE AND DOCUMENTATION ARE
  PROVIDED "AS IS" WITHOUT WARRANTY OF ANY KIND, EITHER EXPRESS OR IMPLIED,
  INCLUDING WITHOUT LIMITATION, ANY WARRANTY OF MERCHANTABILITY, TITLE,
  NON-INFRINGEMENT AND FITNESS FOR A PARTICULAR PURPOSE. IN NO EVENT SHALL
  TEXAS INSTRUMENTS OR ITS LICENSORS BE LIABLE OR OBLIGATED UNDER CONTRACT,
  NEGLIGENCE, STRICT LIABILITY, CONTRIBUTION, BREACH OF WARRANTY, OR OTHER
  LEGAL EQUITABLE THEORY ANY DIRECT OR INDIRECT DAMAGES OR EXPENSES
  INCLUDING BUT NOT LIMITED TO ANY INCIDENTAL, SPECIAL, INDIRECT, PUNITIVE
  OR CONSEQUENTIAL DAMAGES, LOST PROFITS OR LOST DATA, COST OF PROCUREMENT
  OF SUBSTITUTE GOODS, TECHNOLOGY, SERVICES, OR ANY CLAIMS BY THIRD PARTIES
  (INCLUDING BUT NOT LIMITED TO ANY DEFENSE THEREOF), OR OTHER SIMILAR COSTS.

  Should you have any questions regarding your right to use this Software,
  contact Texas Instruments Incorporated at www.TI.com.
**************************************************************************************************/

#line 572 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\bdb\\bdb.h"
 
 
 
 
 
 
 
 
 
 
#line 55 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zdo\\ZDConfig.h"

/*********************************************************************
 * Enable Features
 */
  
//Refer to ZDProfile.h
  //BDB defines the minium requirements on ZDO servces (section 6.6 BDB spec 13-0302-13-00)
#line 80 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zdo\\ZDConfig.h"
  /*
  ACTIVEEP_RSP enabled by default
  NodeDescRsp enabledd by default
  SimpleDescRsp enabled by default
  IEEEaddrRsp enabled by ZDO_IEEEADDR_REQUEST
  nwkAddrRsp enabled by ZDO_NWKADDR_REQUEST
  */
  //Enable Bind request and rsp




//  #define ZDO_MGMT_BIND_REQUEST





//  #define ZDO_MGMT_LQI_REQUEST
#line 106 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zdo\\ZDConfig.h"
  //Enable identify
#line 113 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zdo\\ZDConfig.h"

  
 
#line 222 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zdo\\ZDConfig.h"

  // Normal operation and sample apps only use End Device Bind
  // and Match Request.

  //#define ZDO_NWKADDR_REQUEST
  //#define ZDO_IEEEADDR_REQUEST

  //#define ZDO_NODEDESC_REQUEST
  //#define ZDO_POWERDESC_REQUEST
  //#define ZDO_SIMPLEDESC_REQUEST
  //#define ZDO_ACTIVEEP_REQUEST
  //#define ZDO_COMPLEXDESC_REQUEST
  //#define ZDO_USERDESC_REQUEST
  //#define ZDO_USERDESCSET_REQUEST


  //#define ZDO_SERVERDISC_REQUEST
  //#define ZDO_NETWORKSTART_REQUEST
  //#define ZDO_MANUAL_JOIN

  //#define ZDO_BIND_UNBIND_RESPONSE
  //#define ZDO_COMPLEXDESC_RESPONSE
  //#define ZDO_USERDESC_RESPONSE
  //#define ZDO_USERDESCSET_RESPONSE
  //#define ZDO_SERVERDISC_RESPONSE


  //#define ZDO_MGMT_NWKDISC_REQUEST
  //#define ZDO_MGMT_LQI_REQUEST
  //#define ZDO_MGMT_RTG_REQUEST
  //#define ZDO_MGMT_BIND_REQUEST
  //#define ZDO_MGMT_LEAVE_REQUEST
  //#define ZDO_MGMT_JOINDIRECT_REQUEST

  //#define ZDO_MGMT_NWKDISC_RESPONSE
  //#define ZDO_MGMT_LQI_RESPONSE
  //#define ZDO_MGMT_RTG_RESPONSE

  //#define ZDO_MGMT_LEAVE_RESPONSE
  //#define ZDO_MGMT_JOINDIRECT_RESPONSE




  // Binding needs this request to do a 64 to 16 bit conversion
#line 275 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zdo\\ZDConfig.h"


  
  

/*********************************************************************
 * Constants
 */




  // The application/profile must fill this field out.






  


// Node Description Bitfields








// Simple Description Bitfields
#line 313 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zdo\\ZDConfig.h"

/*********************************************************************
 * Attributes
 */

extern NodeDescriptorFormat_t ZDO_Config_Node_Descriptor;
extern NodePowerDescriptorFormat_t ZDO_Config_Power_Descriptor;

/*********************************************************************
 * Function Prototypes
 */
extern void ZDConfig_InitDescriptors( void );
extern void ZDConfig_UpdateNodeDescriptor( void );
extern void ZDConfig_UpdatePowerDescriptor( void );



/*********************************************************************
*********************************************************************/





#line 55 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zdo\\ZDProfile.h"

/*********************************************************************
 * CONSTANTS
 */





// IEEE_addr_req request types



// ZDO Status Values
#line 84 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zdo\\ZDProfile.h"






// Mgmt_Permit_Join_req fields




// Mgmt_Leave_req fields



// Mgmt_Lqi_rsp - (neighbor table) device type




// Mgmt_Lqi_rsp - (neighbor table) relationship





// Mgmt_Lqi_rsp - (neighbor table) unknown boolean value




// Status fields used by ZDO_ProcessMgmtRtgReq









/*********************************************************************
 * Message/Cluster IDS
 */

// ZDO Cluster IDs



#line 147 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zdo\\ZDProfile.h"

#line 161 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zdo\\ZDProfile.h"

#line 168 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zdo\\ZDProfile.h"

#line 185 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zdo\\ZDProfile.h"



/*********************************************************************
 * TYPEDEFS
 */



typedef struct
{
  osal_event_hdr_t hdr;
  zAddrType_t      srcAddr;
  uint8            wasBroadcast;
  cId_t            clusterID;
  uint8            SecurityUse;
  uint8            TransSeq;
  uint8            asduLen;
  uint16           macDestAddr;
  uint8            *asdu;
  uint16           macSrcAddr;
} zdoIncomingMsg_t;

// This structure is used to build the Mgmt Network Discover Response
typedef struct
{
  uint8 extendedPANID[8];   // The extended PAN ID
  uint16 PANId;            // The network PAN ID
  uint8   logicalChannel;  // Network's channel
  uint8   stackProfile;    // Network's profile
  uint8   version;         // Network's Zigbee version
  uint8   beaconOrder;     // Beacon Order
  uint8   superFrameOrder;
  uint8   permitJoining;   // PermitJoining. 1 or 0
} mgmtNwkDiscItem_t;

// This structure is used to build the Mgmt LQI Response
typedef struct
{
  uint16 nwkAddr;         // device's short address
  uint16 PANId;           // The neighbor device's PAN ID
  uint8  extPANId[8]; // The neighbor device's Extended PanID
  uint8   txQuality;       // Transmit quality
  uint8   rxLqi;           // Receive LQI
} neighborLqiItem_t;


// This structure is used to build the Mgmt_Lqi_rsp
typedef struct
{
  uint16 panID;                  // PAN Id
  uint8  extPanID[8];// Extended Pan ID
  uint8  extAddr[8]; // Extended address
  uint16 nwkAddr;                // Network address
  uint8  devType;                // Device type
  uint8  rxOnIdle;               // RxOnWhenIdle
  uint8  relation;               // Relationship
  uint8  permit;                 // Permit joining
  uint8  depth;                  // Depth
  uint8  lqi;                    // LQI
} ZDP_MgmtLqiItem_t;
// devType, rxOnIdle, relation, are all packed into 1 byte: 18-2=16.



// This structure is used to build the Mgmt Routing Response
// NOTICE: this structure must match "rtgEntry_t" in rtg.h
typedef struct
{
  uint16 dstAddress;     // Destination short address
  uint16 nextHopAddress; // next hop short address
  uint8  expiryTime;     // expiration time - not used for response
  uint8  status;         // route entry status
  uint8  options;
} rtgItem_t;
// expiryTime is not packed & sent OTA.


typedef struct
{
  uint8  TransSeq;
  byte SecurityUse;
  uint16 srcAddr;
  uint16 localCoordinator;
  uint8  ieeeAddr[8];
  uint8  endpoint;
  uint16 profileID;
  uint8  numInClusters;
  uint16 *inClusters;
  uint8  numOutClusters;
  uint16 *outClusters;
} ZDEndDeviceBind_t;

/*********************************************************************
 * GLOBAL VARIABLES
 */

extern byte ZDP_TransID;
extern byte ZDP_TxOptions;

/*********************************************************************
 * MACROS
 */

/*
 * Generic data send function
 */
extern afStatus_t ZDP_SendData( uint8 *transSeq, zAddrType_t *dstAddr, uint16 cmd, byte len,
                                              uint8 *buf, byte SecurityEnable );

/*
 * ZDP_NodeDescReq - Request a Node Description
 *
 * @MT SPI_CMD_ZDO_NODE_DESC_REQ
 * (UInt16 DstAddr,
 *  UInt16 NWKAddrOfInterest,
 *  byte SecuritySuite)
 *
 */




/*
 * ZDP_PowerDescReq - Request a Power Description
 *
 * @MT  SPI_CMD_ZDO_POWER_DESC_REQ
 * (UInt16 DstAddr,
 *  UInt16 NWKAddrOfInterest,
 *  byte SecuritySuit)
 *
 */




/*
 * ZDP_ActiveEPReq - Request a device's endpoint list
 *
 * @MT SPI_CMD_ZDO_ACTIVE_EPINT_REQ
 * (UInt16 DstAddr,
 *  UInt16 NWKAddrOfInterest,
 *  byte SecuritySuite)
 *
 */




/*
 * ZDP_ComplexDescReq - Request a device's complex description
 *
 * @MT SPI_CMD_ZDO_COMPLEX_DESC_REQ
 * (UInt16 DstAddr,
 *  UInt16 NWKAddrOfInterest,
 *  byte SecuritySuite)
 *
 */




/*
 * ZDP_UserDescReq - Request a device's user description
 *
 * @MT SPI_CMD_ZDO_USER_DESC_REQ
 * (UInt16 DstAddr,
 *  UInt16 NWKAddrOfInterest,
 *  byte SecuritySuite)
 *
 */




/*
 * ZDP_BindReq - bind request
 *
 * @MT SPI_CMD_ZDO_BIND_REQ
 * (UInt16 DstAddr,
 *  UInt64 SrcAddress,
 *  byte SrcEndpoint,
 *  uint16 ClusterID,
 *  zAddrType_t *DstAddress,
 *  byte DstEndpoint,
 *  byte SecuritySuite)
 *
 */






/*
 * ZDP_UnbindReq - Unbind request
 *
 * @MT SPI_CMD_ZDO_UNBIND_REQ
 * (UInt16 DstAddr,
 *  UInt64 SrcAddress,
 *  byte SrcEndpoint,
 *  uint16 ClusterID,
 *  zAddrType_t DestinationAddr,
 *  byte DstEndpoint,
 *  byte SecuritySuite)
 *
 */






/*
 * ZDP_MgmtLqiReq - Send a Management LQI Request
 *
 * @MT SPI_CMD_ZDO_MGMT_LQI_REQ
 * (UInt16 DstAddr,
 *  byte StartIndex)
 *
 */



/*
 * ZDP_MgmtRtgReq - Send a Management Routing Table Request
 *
 * @MT SPI_CMD_ZDO_MGMT_RTG_REQ
 * (UInt16 DstAddr,
 *  byte StartIndex)
 *
 */



/*
 * ZDP_MgmtBindReq - Send a Management Binding Table Request
 *
 * @MT SPI_CMD_ZDO_MGMT_BIND_REQ
 * (UInt16 DstAddr,
 *  byte StartIndex)
 *
 */



/*
 * ZDP_ParentAnnceReq - Send a ParentAnnce Request
 */




/*
 * ZDP_ActiveEPRsp - Send an list of active endpoint
 */





/*
 * ZDP_MatchDescRsp - Send an list of endpoint that match
 */





/*
 * ZDP_ComplexDescRsp - This message isn't supported until we fix it.
 */



/*
 * ZDP_UserDescConf - Send a User Descriptor Set Response
 */



/*
 * ZDP_EndDeviceBindRsp - Send a End Device Bind Response
 */



/*
 * ZDP_BindRsp - Send a Bind Response
 */



/*
 * ZDP_UnbindRsp - Send an Unbind Response
 */



/*
 * ZDP_MgmtLeaveRsp - Send a Management Leave Response
 */



/*
 * ZDP_MgmtPermitJoinRsp - Send a Management Permit Join Response
 */



/*
 * ZDP_MgmtDirectJoinRsp - Send a Mgmt_DirectJoining_Rsp Response
 */



/*
 * ZDP_ParentAnnceRsp - Send a ParentAnnceRsp Response
 */




/*********************************************************************
 * FUNCTIONS - API
 */

/*
 * ZDP_NWKAddrOfInterestReq - Send request with NWKAddrOfInterest as parameter
 */
extern afStatus_t ZDP_NWKAddrOfInterestReq( zAddrType_t *dstAddr,
                              uint16 nwkAddr, byte cmd, byte SecurityEnable );
/*
 * ZDP_NwkAddrReq - Request a Network address
 *
 * @MT SPI_CMD_ZDO_NWK_ADDR_REQ
 * (UInt64 IEEEAddress,
 *  byte ReqType,
 *  byte StarIndex,
 *  byte SecurityEnable)
 *
 */
extern afStatus_t ZDP_NwkAddrReq( uint8 *IEEEAddress, byte ReqType,
                               byte StartIndex, byte SecurityEnable );

/*
 * ZDP_IEEEAddrReq - Request an IEEE address
 *
 * @MT SPI_CMD_ZDO_IEEE_ADDR_REQ
 * (UInt16 shortAddr,
 *  byte ReqType,
 *  byte StartIndex,
 *  byte SecurityEnable)
 *
 */
extern afStatus_t ZDP_IEEEAddrReq( uint16 shortAddr, byte ReqType,
                                byte StartIndex, byte SecurityEnable );

/*
 * ZDP_MatchDescReq - Request matching device's endpoint list
 *
 * @MT SPI_CMD_ZDO_MATCH_DESC_REQ
 * (UInt16 DstAddr,
 *  UInt16 NWKAddrOfInterest,
 *  UInt16 ProfileID,
 *  byte NumInClusters,
 *  uint16 InClusterList[15],
 *  byte NumOutClusters,
 *  uint16 OutClusterList[15],
 *  byte SecuritySuite)
 *
 */
extern afStatus_t ZDP_MatchDescReq( zAddrType_t *dstAddr, uint16 nwkAddr,
                                uint16 ProfileID,
                                byte NumInClusters, uint16 *InClusterList,
                                byte NumOutClusters, uint16 *OutClusterList,
                                byte SecurityEnable );

/*
 * ZDP_SimpleDescReq - Request Simple Descriptor
 *
 * @MT SPI_CMD_ZDO_SIMPLE_DESC_REQ
 * (UInt16 DstAddr,
 *  UInt16 NWKAddrOfInterest,
 *  byte Endpoint,
 *  byte Security)
 *
 */
extern afStatus_t ZDP_SimpleDescReq( zAddrType_t *dstAddr, uint16 nwkAddr,
                                    byte ep, byte SecurityEnable );

/*
 * ZDP_UserDescSet - Set the User Descriptor
 *
 * @MT SPI_CMD_ZDO_USER_DESC_SET
 * (UInt16 DstAddr,
 *  UInt16 NWKAddrOfInterest,
 *  byte DescLen,
 *  byte Descriptor[15],
 *  byte SecuritySuite)
 *
 */
extern afStatus_t ZDP_UserDescSet( zAddrType_t *dstAddr, uint16 nwkAddr,
                          UserDescriptorFormat_t *UserDescriptor,
                          byte SecurityEnable );

/*
 * ZDP_ServerDiscReq - Build and send a Server_Discovery_req request message.
 */
afStatus_t ZDP_ServerDiscReq( uint16 serverMask, byte SecurityEnable );

/*
 * ZDP_DeviceAnnce - Device Announce
 *
 * @MT SPI_CMD_ZDO_DEV_ANNCE
 * (UInt16 DevAddr,
 *  byte DeviceAddress,
 *  byte SecuritySuite)
 *
 */
extern afStatus_t ZDP_DeviceAnnce( uint16 nwkAddr, uint8 *IEEEAddr,
                         byte capabilities, byte SecurityEnable );

/*
 * ZDP_ParentAnnce - Parent Announce and Parent Announce Rsp
 */
extern afStatus_t ZDP_ParentAnnce( uint8 *TransSeq,
                                   zAddrType_t *dstAddr,
                                   uint8 numberOfChildren,
                                   uint8 *childInfo,
                                   cId_t clusterID,
                                   uint8 SecurityEnable );

/*
 * ZDP_EndDeviceBindReq - End Device (hand) bind request
 *
 * @MT SPI_CMD_ZDO_END_DEV_BIND_REQ
 * (UInt16 DstAddr,
 *  UInt16 LocalCoordinator,
 *  byte Endpoint,
 *  UInt16 Profile,
 *  byte NumInClusters,
 *  uint16 InClusterList[15],
 *  byte NumOutClusters,
 *  uint16 OutClusterList[15],
 *  byte SecuritySuite)
 *
 */
extern afStatus_t ZDP_EndDeviceBindReq( zAddrType_t *dstAddr,
                              uint16 LocalCoordinator,
                              byte ep,
                              uint16 ProfileID,
                              byte NumInClusters, uint16 *InClusterList,
                              byte NumOutClusters, uint16 *OutClusterList,
                              byte SecurityEnable );

/*
 * ZDP_BindUnbindReq - bind request
 */
extern afStatus_t ZDP_BindUnbindReq( uint16 BindOrUnbind, zAddrType_t *dstAddr,
                            uint8 *SourceAddr, byte SrcEP,
                            cId_t  ClusterID,
                            zAddrType_t *DestinationAddr, byte DstEP,
                            byte SecurityEnable );

/*
 * ZDP_MgmtNwkDiscReq - Send a Management Network Discovery Request
 *
 * @MT SPI_CMD_ZDO_MGMT_NWKDISC_REQ
 * (UInt16 DstAddr,
 *  UInt32 ScanChannels,
 *  byte StartIndex)
 *
 */
extern afStatus_t ZDP_MgmtNwkDiscReq( zAddrType_t *dstAddr,
                            uint32 ScanChannels,
                            byte ScanDuration,
                            byte StartIndex,
                            byte SecurityEnable );

/*
 * ZDP_MgmtDirectJoinReq - Send a Management Direct Join Request
 *
 * @MT SPI_CMD_ZDO_MGMT_DIRECT_JOIN_REQ
 * (UInt16 DstAddr,
 *  UInt64 DeviceAddress,
 *  byte CapInfo)
 *
 */
extern afStatus_t ZDP_MgmtDirectJoinReq( zAddrType_t *dstAddr,
                               uint8 *deviceAddr,
                               byte capInfo,
                               byte SecurityEnable );

/*
 * ZDP_MgmtLeaveReq - Send a Management Leave Request
 *
 * @MT SPI_CMD_ZDO_MGMT_LEAVE_REQ
 * (UInt16 DstAddr,
 *  UInt64 DeviceAddress
 *  uint8 RemoveChildren
 *  uint8 Rejoin
 *  uint8 SecurityEnable)
 */
extern afStatus_t ZDP_MgmtLeaveReq( zAddrType_t *dstAddr,
                                   uint8 *IEEEAddr,
                                   uint8 RemoveChildren,
                                   uint8 Rejoin,
                                   uint8 SecurityEnable );
/*
 * ZDP_MgmtPermitJoinReq - Send a Management Permit Join Request
 *
 * @MT SPI_CMD_ZDO_MGMT_PERMIT_JOIN_REQ
 * (UInt16 DstAddr,
 *  byte duration,
 *  byte TcSignificance)
 *
 */
extern afStatus_t ZDP_MgmtPermitJoinReq( zAddrType_t *dstAddr,
                               byte duration,
                               byte TcSignificance,
                               byte SecurityEnable );

/*
 * ZDP_MgmtNwkUpdateReq - Send a Management NWK Update Request
 *
 * @MT SPI_CMD_ZDO_MGMT_NWK_UPDATE_REQ
 * (uint16 dstAddr,
 *  uint32 ChannelMask,
 *  uint8 ScanDuration,
 *  uint8 ScanCount,
 *  uint16 NwkManagerAddr )
 *
 */
extern afStatus_t ZDP_MgmtNwkUpdateReq( zAddrType_t *dstAddr,
                                        uint32 ChannelMask,
                                        uint8 ScanDuration,
                                        uint8 ScanCount,
                                        uint8 NwkUpdateId,
                                        uint16 NwkManagerAddr );

/*********************************************************************
 * @fn      ZDP_AddrRsp
 *
 * @brief   Build and send a NWK_addr_rsp or IEEE_addr_rsp message.
 *
 * @param   cId - ClusterID of the rsp, either NWK_addr_rsp or IEEE_addr_rsp.
 * @param   seq - Message sequence number of the corresponding request.
 * @param   dst - Destination address for the response.
 * @param   stat - Response status: ZDP_SUCCESS or other value from ZDProfile.h
 * @param   ieee - 64-bit IEEE address of the response.
 * @param   reqType - Type of response requested (single, extended, etc.)
 * @param   nwkAddr - 16-bit network address of the response.
 * @param   devCnt  - Number of associated devices in the device address list.
 * @param   strtIdx - Starting index into the dev addr array if extended rsp.
 * @param   devAddr - Array of 16-bit network addresses of the associated devs.
 * @param   secOpt  - Security Enable Options.
 *
 * @return  afStatus_t
 */
afStatus_t ZDP_AddrRsp( byte cId, byte seq, zAddrType_t *dst, byte stat,
  uint8 *ieee, byte reqType, uint16 nwkAddr, byte devCnt, byte strtIdx,
  uint16 *devAddr, byte secOpt );

/*
 * ZDP_NodeDescMsg - Send a Node Descriptor message.
 */
extern afStatus_t ZDP_NodeDescMsg( zdoIncomingMsg_t *inMsg,
                    uint16 nwkAddr, NodeDescriptorFormat_t *pNodeDesc );

/*
 * ZDP_PowerDescMsg - Send a Node Power Descriptor message.
 */
extern afStatus_t ZDP_PowerDescMsg( zdoIncomingMsg_t *inMsg,
 uint16 nwkAddr, NodePowerDescriptorFormat_t *pPowerDesc );

/*
 * ZDP_SimpleDescMsg - Send a Simple Descriptor message.
 */
extern afStatus_t ZDP_SimpleDescMsg( zdoIncomingMsg_t *inMsg,
                     byte Status, SimpleDescriptionFormat_t *pSimpleDesc );

/*
 * ZDP_EPRsp - Send a list of endpoint
 */
extern afStatus_t ZDP_EPRsp( uint16 MsgType, byte TransSeq, zAddrType_t *dstAddr, byte Status,
                                uint16 nwkAddr, byte Count, uint8 *pEPList,
                                byte SecurityEnable );

/*
 * ZDP_GenericRsp - Sends a response message with only the parameter response
 *                                     byte and the addr of interest for data.
 */
extern afStatus_t ZDP_GenericRsp( byte TransSeq, zAddrType_t *dstAddr,
                    byte status, uint16 aoi, uint16 rspID, byte SecurityEnable );

/*
 * ZDP_MgmtNwkDiscRsp - Sends the Management Network Discovery Response.
 */
extern afStatus_t ZDP_MgmtNwkDiscRsp( byte TransSeq, zAddrType_t *dstAddr,
                            byte Status,
                            byte NetworkCount,
                            byte StartIndex,
                            byte NetworkCountList,
                            networkDesc_t *NetworkList,
                            byte SecurityEnable );

/*
 * ZDP_MgmtLqiRsp - Sends the Management LQI Response.
 */
extern ZStatus_t ZDP_MgmtLqiRsp( byte TransSeq, zAddrType_t *dstAddr,
                          byte Status,
                          byte NeighborLqiEntries,
                          byte StartIndex,
                          byte NeighborLqiCount,
                          ZDP_MgmtLqiItem_t* NeighborList,
                          byte SecurityEnable );

/*
 * ZDP_MgmtRtgRsp - Sends the Management Routing Response.
 */
extern ZStatus_t ZDP_MgmtRtgRsp( byte TransSeq, zAddrType_t *dstAddr,
                            byte Status,
                            byte RoutingTableEntries,
                            byte StartIndex,
                            byte RoutingListCount,
                            rtgItem_t *RoutingTableList,
                            byte SecurityEnable );

/*
 * ZDP_MgmtBindRsp - Sends the Management Binding Response.
 */
extern ZStatus_t ZDP_MgmtBindRsp( byte TransSeq, zAddrType_t *dstAddr,
                            byte Status,
                            byte BindingTableEntries,
                            byte StartIndex,
                            byte BindingTableListCount,
                            apsBindingItem_t *BindingTableList,
                            byte SecurityEnable );
/*
 * ZDP_MgmtNwkUpdateNotify - Sends the Management Netwotk Update Notify.
 */
extern afStatus_t ZDP_MgmtNwkUpdateNotify( uint8 TransSeq, zAddrType_t *dstAddr,
                                    uint8 status, uint32 scannedChannels,
                                    uint16 totalTransmissions, uint16 transmissionFailures,
                                    uint8 listCount, uint8 *energyValues, uint8 txOptions,
                                    uint8 securityEnable );

/*
 * ZDP_UserDescRsp - Sends the user descriptor response message.
 */
extern ZStatus_t ZDP_UserDescRsp( byte TransSeq, zAddrType_t *dstAddr,
                uint16 nwkAddrOfInterest, UserDescriptorFormat_t *userDesc,
                byte SecurityEnable );

/*
 * ZDP_ServerDiscRsp - Build and send the User Decriptor Response.
 */
ZStatus_t ZDP_ServerDiscRsp( byte transID, zAddrType_t *dstAddr, byte status,
                           uint16 aoi, uint16 serverMask, byte SecurityEnable );

/*
 * ZDP_IncomingData - Incoming data callback from AF layer
 */
extern void ZDP_IncomingData( afIncomingMSGPacket_t *pData );

extern ZStatus_t ZDO_RegisterForZDOMsg( uint8 taskID, uint16 clusterID );
extern ZStatus_t ZDO_RemoveRegisteredCB( uint8 taskID, uint16 clusterID );


/*********************************************************************
*********************************************************************/





#line 62 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\bdb\\bdb.h"


  
#line 77 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\bdb\\bdb.h"


//Configured per device  
#line 89 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\bdb\\bdb.h"
  

   

/*********************************************************************
 * MACROS
 */
  
// bdbNodeCommissioningCapability MACROS  
#line 116 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\bdb\\bdb.h"
  


//Initialization structure for bdb attributes
#line 167 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\bdb\\bdb.h"

//Commissioning Modes
#line 176 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\bdb\\bdb.h"
                                         



                                              


// bdbNodeJoinLinkKeyType













// New respondents require to get simple descritor request from remote device.
// If the respondent has a matching cluster a bind request is created, for which 
// if IEEE addr is missing then the entry is process to get its IEEE Addr by 
// sending an IEEE Addr Req
// Attempt counter also is used to designed which type of request will be send 
// by the usage of the mask FINDING_AND_BINDING_MISSING_IEEE_ADDR and the 
// assupmtion that the retries will not excede 36 attempts
   





 /*********************************************************************
 * CONSTANTS
 */

//Poll rate for Trust Center Link Key exchange process


// Zigbee Home Automation Profile Identification



// Define if Touchlink Target device will use fixed or random 
// channel from bdbcTLPrimaryChannelSet during commissioning
// when is Factory New (development only).



// set TOUCHLINK_CH_OFFSET to Ch_Plus_1, Ch_Plus_2 or Ch_Plus_3 to shift
// the primary channel set (development only), allowing testing of multiple 
// touchlink devices without interference ONLY for testing propouses. if set 
// to No_Ch_offset (default) then no shift is applied.


//BDB Attribute initialization constants
#line 241 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\bdb\\bdb.h"



//Constants for CRC calculations






// TOUCHLINK Profile Constants
#line 258 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\bdb\\bdb.h"

// TOUCHLINK Channels (standard)





#line 274 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\bdb\\bdb.h"

 /*********************************************************************
 * TYPEDEFS
 */

enum
{
BDB_COMMISSIONING_STATE_START_RESUME,            //Start/Resume the commissioning process according to commissionig modes
BDB_COMMISSIONING_STATE_TC_LINK_KEY_EXCHANGE,    //Perform the TC Link key exchange
BDB_COMMISSIONING_STATE_TL,                      //Perform Touchlink procedure as initiator
BDB_COMMISSIONING_STATE_JOINING,                 //Performs nwk discovery, joining attempt and nwk key reception
BDB_COMMISSIONING_STATE_STEERING_ON_NWK,         //Send mgmt permit joining
BDB_COMMISSIONING_STATE_FORMATION,               //Perform formtation procedure
BDB_COMMISSIONING_STATE_FINDING_BINDING,         //Perform Finding and binding procedure
BDB_INITIALIZATION,                              //Initialization process, for ZC/ZR means silent rejoin, for ZED nwk rejoin
BDB_PARENT_LOST,                                 //Parent lost, ask app to nwk Rejoin or giveup and reset

//Non-State related messages
BDB_TC_LINK_KEY_EXCHANGE_PROCESS,                //TC Notifications for TC link key exchange process with joining devices
BDB_NOTIFY_USER,                                 //Message to notify user about processing in BDB
BDB_ZDO_CB_MSG = 0xD3                                //To process ZDO CB Msg
};
    
 
typedef struct
{
uint32 bdbSecondaryChannelSet;
uint32 bdbPrimaryChannelSet;
uint16 bdbCommissioningGroupID;
uint8  bdbCommissioningStatus; 
uint8  bdbCommissioningMode;
uint8  bdbNodeCommissioningCapability;
uint8  bdbScanDuration;
_Bool   bdbNodeIsOnANetwork;

_Bool   bdbJoinUsesInstallCodeKey;
uint8  bdbTrustCenterNodeJoinTimeout;
_Bool   bdbTrustCenterRequireKeyExchange;
#line 319 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\bdb\\bdb.h"
}bdbAttributes_t;


typedef struct respondentData
{
  afAddrType_t               data;
  uint8                      attempts;
  SimpleDescriptionFormat_t* SimpleDescriptor;
  struct respondentData*     pNext;
}bdbFindingBindingRespondent_t;



typedef struct bdb_joiningDeviceList_node
{
uint16 parentAddr;
uint8  bdbJoiningNodeEui64[8];
uint8  NodeJoinTimeout;
struct bdb_joiningDeviceList_node*  nextDev;
}bdb_joiningDeviceList_t;

//BDB Events
#line 350 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\bdb\\bdb.h"

//Msg event status






enum
{
BDB_JOIN_EVENT_NWK_DISCOVERY,
BDB_JOIN_EVENT_ASSOCIATION,
BDB_JOIN_EVENT_NO_NWK_KEY,
BDB_JOIN_EVENT_OTHER,
};

enum
{
BDB_TC_LINK_KEY_EXCHANGE_NOT_ACTIVE,
BDB_REQ_TC_STACK_VERSION,
BDB_REQ_TC_LINK_KEY,
BDB_REQ_VERIFY_TC_LINK_KEY,
BDB_TC_EXCHANGE_NEXT_STATE=1,
};

typedef struct
{
  osal_event_hdr_t hdr;
  uint8  buf[1];
}bdbInMsg_t;


enum 
{
BDB_JOIN_STATE_NWK_DISC,
BDB_JOIN_STATE_ASSOC,
BDB_JOIN_STATE_WAITING_NWK_KEY,
};

typedef struct
{
uint8    bdbCommissioningState;
uint8    bdbTCExchangeState;
uint8    bdbJoinState;
uint8    bdb_ParentLostSavedState;      //Commissioning state to be restore after parent is found
}bdbCommissioningProcedureState_t;

typedef struct
{
  zAddrType_t dstAddr;
  uint8       ep;
  uint16      clusterId;
}bdbBindNotificationData_t;

typedef void (*tlGCB_TargetEnable_t)( uint8 enable );

/*********************************************************************
 * GLOBAL VARIABLES
 */
 
extern byte bdb_TaskID;

extern bdbAttributes_t bdbAttributes;

extern uint8 touchLinkInitiator_TaskID;

extern epList_t *bdb_HeadEpDescriptorList;

extern epList_t *bdb_CurrEpDescriptorList;

extern bdbCommissioningProcedureState_t bdbCommissioningProcedureState;

extern uint8 bdb_ZclTransactionSequenceNumber;

extern uint8 bdb_FB_InitiatorCurrentCyclesNumber;

extern bdbFindingBindingRespondent_t *pRespondentHead;

extern bdbFindingBindingRespondent_t *pRespondentCurr;

extern bdbFindingBindingRespondent_t *pRespondentNext;

















/*********************************************************************
 * FUNCTION MACROS
 */
 



/*********************************************************************
 * FUNCTIONS
 */
extern void bdb_reportCommissioningState(uint8 bdbCommissioningState, _Bool didSuccess);
extern void bdb_setFN(void);
extern void bdb_touchlinkSendFNReset( void );
extern void bdb_setNodeIsOnANetwork(_Bool isOnANetwork);
extern void bdb_nwkFormationAttempt(_Bool didSucess);
extern void bdb_nwkDiscoveryAttempt(_Bool didSuccess);
extern void bdb_nwkAssocAttemt(_Bool didSuccess);
extern ZStatus_t bdb_rejoinNwk(void);
extern void touchLinkInitiator_ResetToFNProcedure( void );
extern void bdb_tcLinkKeyExchangeAttempt(_Bool didSuccess, uint8 bdbTCExchangeState);
extern void bdb_SendMsg(uint8 taskID, uint8 toCommissioningState,uint8 status, uint8 len, uint8 *buf);
extern void bdb_setNodeJoinLinkKeyType(uint8 KeyType);  
extern bdbFindingBindingRespondent_t* bdb_AddRespondentNode( bdbFindingBindingRespondent_t **pHead, zclIdentifyQueryRsp_t *pCmd );
extern void bdb_CreateRespondentList( bdbFindingBindingRespondent_t **pHead );



extern ZStatus_t bdb_TCAddJoiningDevice(uint16 parentAddr, uint8* JoiningExtAddr);
extern void bdb_TCjoiningDeviceComplete(uint8* JoiningExtAddr);


ZStatus_t bdb_addInstallCode(uint8* pInstallCode, uint8* pExt);

/*
 * @brief   Register the Simple descriptor. This function also registers 
 *          the profile's cluster conversion table.
 */
void bdb_RegisterSimpleDescriptor( SimpleDescriptionFormat_t *simpleDesc );

/*
 * @brief   Sends Identify query from the specified endpoint
 */
extern ZStatus_t bdb_SendIdentifyQuery( uint8 endpoint );

/*
 * @brief   This function free reserved memory for respondent list
 */
extern void bdb_zclRespondentListClean( bdbFindingBindingRespondent_t **pHead );



/*
 * @brief   Process the respondent list by sending Simple Descriptor request to 
 *          devices respondent in the list. Also send IEEE Addr Req to those 
 *          device for which a bind is created buy IEEE addr is missing.
 */
extern void bdb_ProcessRespondentList( void );

/*
 * @brief   Gives the Ep Type accourding to application clusters in
 *          simple descriptor
 */
extern uint8 bdb_zclFindingBindingEpType( endPointDesc_t *epDesc );

/*
 * @brief   Send out a Network Join Router or End Device Request command.
 *          using the selected Target.
 */
extern ZStatus_t bdb_Initiator_SendNwkJoinReq( void );

/*
 * @brief   Callback from the ZCL General Cluster Library when
 *          it received an Identity Command for this application.
 */
extern void bdb_ZclIdentifyCmdInd( uint16 identifyTime, uint8 endpoint );

/*
 * @brief   Callback from the ZCL General Cluster Library when
 *          it received an Identity Query Response Command for this 
 *          application.
 */
extern void bdb_ZclIdentifyQueryCmdInd( zclIdentifyQueryRsp_t *pCmd );

/*
 * @brief   Restore nwk parameters to invalid if the device is not on a network
 */
void bdb_ClearNetworkParams(void);

/*
 * @brief       Notify bdb that connection with parent is lost
 */
void bdb_parentLost(void);

/*
 * @brief       Restore the state of child device after parent lost
 */
void bdb_NetworkRestoredResumeState(void);

/*
 * @brief   Set the endpoint list to the active endpoint selected by the application for F&B process
 */
endPointDesc_t* bdb_setEpDescListToActiveEndpoint(void);

/*
 * @brief   Clean the F&B initiator process and reports the status to bdb state machine
 */
void bdb_exitFindingBindingWStatus( uint8 status);

/*
 * @brief   This function free reserved memory for respondent list
 */
void bdb_zclRespondentListClean( bdbFindingBindingRespondent_t **pHead );

 /*
  * @brief       Set channel and save it in Nv for joining/formation operations
  */
extern void bdb_setChannel(uint32 channel);







 
 
 
 
 
 
 
 
 
 
#line 53 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\bdb\\bdb_interface.h"
 
 /*********************************************************************
 * CONSTANTS
 */
 


   

//bdbTCLinkKeyExchangeMethod


   
//Status notifications on APS TC Link exchange process for a joining device










 /*********************************************************************
 * CONFIGURATION MACROS
 */
 
 /**********************
 * General configuration
 */

//Constants used by all nodes



//Define if ZR devices will perform classical formation procedure or not (the network formed would be Distributed Network)

  
//Define how IC are introduced see


//Time after which the device will reset itself after failining on 
//TCLK exchange procedure (more than BDB_DEFAULT_TC_LINK_KEY_EXCHANGE_ATTEMPS_MAX 
//attempts for the same request or Parent Lost during TCLK exchange process).
//This reset will perform a FN reset




//Default values for BDB attributes 
#line 112 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\bdb\\bdb_interface.h"






 /******************
 * F&B configuration
 */
//Your JOB: Set this value according to your application
//Initiator devices in F&B procedure may enable this macro to perfom the searching as a periodic task
//for up to 3 minutes with a period of FINDING_AND_BINDING_PERIODIC_TIME between discovery attempts



// Number of attemtps that will be done to retrieve the simple desc from a target 
// device or the IEEE Address if this is unknown. The number of attempts cannot 
// be greater than 36



//Your JOB: Set this value according to your application
//This defines the time that initiator device will wait for Indentify query response 
//and simple descriptor from target devices. Consider Identify Query is broadcast while Simple Desc is unicast
//Consider that ZED will have to wait longer since their responses will need to 
//be pooled and will be dependent of the number of targets that is expected to be found
#line 145 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\bdb\\bdb_interface.h"


 /******************
 * Touchlink configuration
 */

/** Received signal strength threshold **/
// Manufacturer specific threshold (greater than -128),
// do not respond to Touch-link scan request if reached



 
// Pre-programmed RSSI correction offset (0x00-0x20)




/** Pre-Installed Keys **/













// For certification only:




// For internal EP's simple descriptor





 /******************
 * Reporting attributes configuration
 */
#line 214 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\bdb\\bdb_interface.h"

/*********************************************************************
 * ENUM
 */
 

enum
{
  BDB_COMMISSIONING_INITIALIZATION,
  BDB_COMMISSIONING_NWK_STEERING,
  BDB_COMMISSIONING_FORMATION,
  BDB_COMMISSIONING_FINDING_BINDING,
  BDB_COMMISSIONING_TOUCHLINK,
  BDB_COMMISSIONING_PARENT_LOST,
};


enum
{
  BDB_COMMISSIONING_SUCCESS,       
  BDB_COMMISSIONING_IN_PROGRESS,   
  BDB_COMMISSIONING_NO_NETWORK,          
  BDB_COMMISSIONING_TL_TARGET_FAILURE,
  BDB_COMMISSIONING_TL_NOT_AA_CAPABLE,
  BDB_COMMISSIONING_TL_NO_SCAN_RESPONSE,
  BDB_COMMISSIONING_TL_NOT_PERMITTED,
  BDB_COMMISSIONING_TCLK_EX_FAILURE,              //Many attempts made and failed, or parent lost during the TCLK exchange
  BDB_COMMISSIONING_FORMATION_FAILURE,
  BDB_COMMISSIONING_FB_TARGET_IN_PROGRESS,        //No callback from bdb when the identify time runs out, the application can figure out from Identify time callback
  BDB_COMMISSIONING_FB_INITITATOR_IN_PROGRESS,
  BDB_COMMISSIONING_FB_NO_IDENTIFY_QUERY_RESPONSE,
  BDB_COMMISSIONING_FB_BINDING_TABLE_FULL,
  BDB_COMMISSIONING_NETWORK_RESTORED,               
  BDB_COMMISSIONING_FAILURE,              //Generic failure status for no commissioning mode supported, not allowed, invalid state to perform commissioning
};



 /*********************************************************************
 * TYPEDEFS
 */
 
typedef struct
{
  uint8  bdbCommissioningStatus;
  uint8  bdbCommissioningMode;
  uint8  bdbRemainingCommissioningModes;
}bdbCommissioningModeMsg_t;


typedef struct
{
  uint8 status;                  //status: BDB_TC_LK_EXCH_PROCESS_JOINING
  uint8 extAddr[8];
}bdb_TCLinkKeyExchProcess_t;



typedef void (*bdbGCB_IdentifyTimeChange_t)( uint8 endpoint );
typedef void (*bdbGCB_BindNotification_t)( bdbBindNotificationData_t *bindData );
typedef void (*bdbGCB_CommissioningStatus_t)(bdbCommissioningModeMsg_t *bdbCommissioningModeMsg);
typedef void (*bdbGCB_CBKETCLinkKeyExchange_t)( void );
typedef void (*bdbGCB_TCLinkKeyExchangeProcess_t) (bdb_TCLinkKeyExchProcess_t* bdb_TCLinkKeyExchProcess);
typedef void (*bdbGCB_FilterNwkDesc_t) (networkDesc_t *pBDBListNwk, uint8 count);
 


/*********************************************************************
 * GLOBAL VARIABLES
 */



 
extern _Bool touchLinkTargetEnabled;

 /*********************************************************************
 * FUNCTION MACROS
 */

/*
 * Initialize the device with persistant data. Restore nwk (Silent rejoin for ZC and ZR, Rejoin for ZED), and resume reporting attributes.
 */



 /*********************************************************************
 * FUNCTIONS
 */
   
 /*****************************
 * GENERAL API
 */

/*
 * @brief   Event Process for the task
 */
UINT16 bdb_event_loop( byte task_id, UINT16 events );

/*
 * @brief   Initialization for the task
 */
void bdb_Init( byte task_id );
 
/*
 * @brief   Start the commissioning process setting the commissioning mode given.
 */
void bdb_StartCommissioning(uint8 mode);

/*
 * @brief   Set the endpoint which will perform the finding and binding (either Target or Initiator)
 */
ZStatus_t bdb_SetIdentifyActiveEndpoint(uint8 activeEndpoint);

/*
 * @brief   Stops Finding&Binding for initiator devices. The result of this process 
 * is reported in bdb notifications callback.
 */  
void bdb_StopInitiatorFindingBinding(void);

/*  
 * @brief   Get the next ZCL Frame Counter for packet sequence number
 */
uint8 bdb_getZCLFrameCounter(void);

/*
 * @brief   Application interface to perform BDB Reset to FN.
 */
void bdb_resetLocalAction(void);

/*
 * @brief   Set the primary or seconday channel for discovery or formation procedure
 */
void bdb_setChannelAttribute(_Bool isPrimaryChannel, uint32 channel);

/*
 * @brief   Register an Application's Identify Time change callback function
 *          to let know the application when identify is active or not.
 */
void bdb_RegisterIdentifyTimeChangeCB( bdbGCB_IdentifyTimeChange_t pfnIdentifyTimeChange );

/*
 * @brief   Register an Application's notification callback function to let 
 *          know the application when a new bind is added to the binding table.
 */
void bdb_RegisterBindNotificationCB( bdbGCB_BindNotification_t pfnBindNotification );

/*
 * @brief   Get the F&B initiator status for periodic requests.
 */
void bdb_GetFBInitiatorStatus(uint8 *RemainingTime, uint8* AttemptsLeft);

/*
 * @brief   Register a callback in which the status of the procedures done in
 *          BDB commissioning process will be reported
 */
void bdb_RegisterCommissioningStatusCB( bdbGCB_CommissioningStatus_t bdbGCB_CommissioningStatus );

/*
 * @brief   Returns the state of bdbNodeIsOnANetwork attribute
 */
_Bool bdb_isDeviceNonFactoryNew(void);

/*
 * @brief   Sets the commissioning groupd ID
 */
void bdb_setCommissioningGroupID(uint16 groupID);

 /*
  * @brief   Creates a CRC for the install code passed.
  */
 uint16 bdb_GenerateInstallCodeCRC(uint8 *installCode);
 
/*
 * @brief   Returns the state of bdbTrustCenterRequireKeyExchange attribute
 */
_Bool bdb_doTrustCenterRequireKeyExchange(void);

 /*****************************
 * REPORTING ATTRIBUTES API
 */

#line 409 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\bdb\\bdb_interface.h"

 /*****************************
 * Trust Center API  (ZC)
 */



/*
 * @brief   Set BDB attribute bdbJoinUsesInstallCodeKey.
 */
void bdb_setJoinUsesInstallCodeKey(_Bool set);

/*
 * @brief   Set the bdb_setTCRequireKeyExchange attribute
 */
void bdb_setTCRequireKeyExchange(_Bool isKeyExchangeRequired);



/*
 * bdb_addInstallCode interface.
 */
ZStatus_t bdb_addInstallCode(uint8* pInstallCode, uint8* pExt);

/*
 * @brief   Register a callback to receive notifications on the joining devices 
 *          and its status on TC link key exchange. 
 */
void bdb_RegisterTCLinkKeyExchangeProcessCB( bdbGCB_TCLinkKeyExchangeProcess_t bdbGCB_TCLinkKeyExchangeProcess );





 /*****************************
 * Joining devices API  (ZR ZED)
 */

/*
 * @brief   Register an Application's Enable/Disable callback function. 
 *          Refer to touchLinkTarget_EnableCommissioning to enable/disable TL as target
 */
void bdb_RegisterTouchlinkTargetEnableCB( tlGCB_TargetEnable_t pfnTargetEnableChange );

 /*
 * @brief   Enable the reception of Commissioning commands.
 */
void touchLinkTarget_EnableCommissioning( uint32 timeoutTime );


 /*
 * @brief   Disable TouchLink commissioning on a target device.
 */
void touchLinkTarget_DisableCommissioning( void );

 /*
 * @brief   Get the remaining time for TouchLink on a target device.
 */
uint32 touchLinkTarget_GetTimer( void );

/*
 * @brief   Set the active centralized key to be used, Global or IC derived
 */
ZStatus_t bdb_setActiveCentralizedLinkKey(_Bool useGlobal, uint8* pBuf);


/*
 * @brief   Register a callback in which the TC link key exchange procedure will 
 *          be performed by application.  The result from this operation must be notified to using the 
 *          bdb_CBKETCLinkKeyExchangeAttempt interface.
 *          NOTE: NOT CERTIFIABLE AT THE MOMENT OF THIS RELEASE
 */
void bdb_RegisterCBKETCLinkKeyExchangeCB( bdbGCB_CBKETCLinkKeyExchange_t bdbGCB_CBKETCLinkKeyExchange );

/*
 * @brief   Tell BDB module the result of the TC link key exchange, to try
 *          the default process or to keep going with the joining process.
 */
void bdb_CBKETCLinkKeyExchangeAttempt(_Bool didSucces);


/*
 * @brief   Register a callback in which the application gets the list of network
 *          descriptors got from active scan.
 *          Use bdb_nwkDescFree to release the network descriptors that are not 
 *          of interest and leave those which are to be attempted.
 */
void bdb_RegisterForFilterNwkDescCB(bdbGCB_FilterNwkDesc_t bdbGCB_FilterNwkDesc);

/*
 * @brief   This function frees a network descriptor.
 */
ZStatus_t bdb_nwkDescFree(networkDesc_t* nodeDescToRemove);

/*
 * @brief   General function to allow stealing when performing TL as target
 */
void bdb_TouchlinkSetAllowStealing( _Bool allow );

/*
 * @brief   General function to get allow stealing value
 */
_Bool bdb_TouchlinkGetAllowStealing( void );

 /*****************************
 * ZED API
 */
#line 523 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\bdb\\bdb_interface.h"

/*************************************************************************/





#line 57 "F:\\Workspace\\zigbfuzz\\depenInfer/zcl.c"

#line 1 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl_green_power.h"
/**************************************************************************************************
  Filename:       zcl_green_power.h
  Revised:        $Date: 2014-10-14 13:03:14 -0700 (Tue, 14 Oct 2014) $
  Revision:       $Revision: 40629 $

  Description:    This file contains the ZCL General definitions.


  Copyright 2006-2014 Texas Instruments Incorporated. All rights reserved.

  IMPORTANT: Your use of this Software is limited to those specific rights
  granted under the terms of a software license agreement between the user
  who downloaded the software, his/her employer (which must be your employer)
  and Texas Instruments Incorporated (the "License").  You may not use this
  Software unless you agree to abide by the terms of the License. The License
  limits your use, and you acknowledge, that the Software may not be modified,
  copied or distributed unless embedded on a Texas Instruments microcontroller
  or used solely and exclusively in conjunction with a Texas Instruments radio
  frequency transceiver, which is integrated into your product.  Other than for
  the foregoing purpose, you may not use, reproduce, copy, prepare derivative
  works of, modify, distribute, perform, display or sell this Software and/or
  its documentation for any purpose.

  YOU FURTHER ACKNOWLEDGE AND AGREE THAT THE SOFTWARE AND DOCUMENTATION ARE
  PROVIDED "AS IS" WITHOUT WARRANTY OF ANY KIND, EITHER EXPRESS OR IMPLIED,
  INCLUDING WITHOUT LIMITATION, ANY WARRANTY OF MERCHANTABILITY, TITLE,
  NON-INFRINGEMENT AND FITNESS FOR A PARTICULAR PURPOSE. IN NO EVENT SHALL
  TEXAS INSTRUMENTS OR ITS LICENSORS BE LIABLE OR OBLIGATED UNDER CONTRACT,
  NEGLIGENCE, STRICT LIABILITY, CONTRIBUTION, BREACH OF WARRANTY, OR OTHER
  LEGAL EQUITABLE THEORY ANY DIRECT OR INDIRECT DAMAGES OR EXPENSES
  INCLUDING BUT NOT LIMITED TO ANY INCIDENTAL, SPECIAL, INDIRECT, PUNITIVE
  OR CONSEQUENTIAL DAMAGES, LOST PROFITS OR LOST DATA, COST OF PROCUREMENT
  OF SUBSTITUTE GOODS, TECHNOLOGY, SERVICES, OR ANY CLAIMS BY THIRD PARTIES
  (INCLUDING BUT NOT LIMITED TO ANY DEFENSE THEREOF), OR OTHER SIMILAR COSTS.

  Should you have any questions regarding your right to use this Software,
  contact Texas Instruments Incorporated at www.TI.com.
**************************************************************************************************/









/*********************************************************************
 * INCLUDES
 */
#line 1 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\gp\\cGP_stub.h"
/**************************************************************************************************
  Filename:       cGP_stub.h
  Revised:        $Date: 2016-05-23 11:51:49 -0700 (Mon, 23 May 2016) $
  Revision:       $Revision: - $

  Description:    This file contains the common Green Power stub definitions.


  Copyright 2006-2014 Texas Instruments Incorporated. All rights reserved.

  IMPORTANT: Your use of this Software is limited to those specific rights
  granted under the terms of a software license agreement between the user
  who downloaded the software, his/her employer (which must be your employer)
  and Texas Instruments Incorporated (the "License").  You may not use this
  Software unless you agree to abide by the terms of the License. The License
  limits your use, and you acknowledge, that the Software may not be modified,
  copied or distributed unless embedded on a Texas Instruments microcontroller
  or used solely and exclusively in conjunction with a Texas Instruments radio
  frequency transceiver, which is integrated into your product.  Other than for
  the foregoing purpose, you may not use, reproduce, copy, prepare derivative
  works of, modify, distribute, perform, display or sell this Software and/or
  its documentation for any purpose.

  YOU FURTHER ACKNOWLEDGE AND AGREE THAT THE SOFTWARE AND DOCUMENTATION ARE
  PROVIDED "AS IS" WITHOUT WARRANTY OF ANY KIND, EITHER EXPRESS OR IMPLIED,
  INCLUDING WITHOUT LIMITATION, ANY WARRANTY OF MERCHANTABILITY, TITLE,
  NON-INFRINGEMENT AND FITNESS FOR A PARTICULAR PURPOSE. IN NO EVENT SHALL
  TEXAS INSTRUMENTS OR ITS LICENSORS BE LIABLE OR OBLIGATED UNDER CONTRACT,
  NEGLIGENCE, STRICT LIABILITY, CONTRIBUTION, BREACH OF WARRANTY, OR OTHER
  LEGAL EQUITABLE THEORY ANY DIRECT OR INDIRECT DAMAGES OR EXPENSES
  INCLUDING BUT NOT LIMITED TO ANY INCIDENTAL, SPECIAL, INDIRECT, PUNITIVE
  OR CONSEQUENTIAL DAMAGES, LOST PROFITS OR LOST DATA, COST OF PROCUREMENT
  OF SUBSTITUTE GOODS, TECHNOLOGY, SERVICES, OR ANY CLAIMS BY THIRD PARTIES
  (INCLUDING BUT NOT LIMITED TO ANY DEFENSE THEREOF), OR OTHER SIMILAR COSTS.

  Should you have any questions regarding your right to use this Software,
  contact Texas Instruments Incorporated at www.TI.com.
**************************************************************************************************/









  
  
  
/*********************************************************************
 * INCLUDES
 */
  



  
  
  
/*********************************************************************
 * MACROS
 */
  

  
//GP Nwk FrameControl  
//Masks  




//Possitions




   






//GP ExtendedNwkFrameControl   


//defined by application   
#line 97 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\gp\\cGP_stub.h"

   



   












  

   




//TxOptions for GP-Data.Request
#line 129 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\gp\\cGP_stub.h"


//TxOptions for cGP-Data.Request










 /*********************************************************************
 * CONSTANTS
 */
 
  

 /*********************************************************************
 * TYPEDEFS
 */

enum
{
GP_MAC_MCPS_DATA_CNF, //Related to Common GP stub  
GP_MAC_MCPS_DATA_IND, //Related to Common GP stub
DGP_DATA_IND,      //Related to dedicated GP stub
DLPED_DATA_IND,    //Related to DLPE  not supported
GP_DATA_IND,       //Related to GP endpoint  
GP_DATA_REQ,       //Related to GP endpoint  
GP_DATA_CNF,       //Related to GP endpoint  
GP_SEC_REQ,        //Related to GP endpoint  
GP_SEC_RSP,        //Related to GP endpoint  
};


enum
{
GP_DATA_CNF_TX_QUEUE_FULL,
GP_DATA_CNF_ENTRY_REPLACED,
GP_DATA_CNF_ENTRY_ADDED,
GP_DATA_CNF_ENTRY_EXPIRED,
GP_DATA_CNF_ENTRY_REMOVED,
GP_DATA_CNF_GPDF_SENDING_FINALIZED,
};

enum
{
GP_SEC_RSP_DROP_FRAME,
GP_SEC_RSP_MATCH,
GP_SEC_RSP_PASS_UNPROCESSED,
GP_SEC_RSP_TX_THEN_DROP,
GP_SEC_RSP_ERROR,
};

enum
{
GP_DATA_IND_STATUS_SECURITY_SUCCESS,
GP_DATA_IND_STATUS_NO_SECURITY,
GP_DATA_IND_STATUS_COUNTER_FAILURE,
GP_DATA_IND_STATUS_AUTH_FAILURE,
GP_DATA_IND_STATUS_UNPROCESSED
};


/* GP event header type */
typedef struct
{
  uint8   event;              /* MAC event */
  uint8   status;             /* MAC status */
} gpEventHdr_t;



typedef struct
{
uint8                  dGPStubHandle;
struct gp_DataInd_tag  *next;
uint32                 timeout;
}gp_DataIndSecReq_t;

typedef struct gp_DataInd_tag
{
gpEventHdr_t        hdr;
gp_DataIndSecReq_t  SecReqHandling;
uint32              timestamp;
uint8               status;
int8                Rssi;
uint8               LinkQuality;
uint8               SeqNumber;
sAddr_t             srcAddr;
uint16              srcPanID;
uint8               appID;
uint8               GPDFSecLvl;
uint8               GPDFKeyType;
_Bool                AutoCommissioning;
_Bool                RxAfterTx;
uint32              SrcId;
uint8               EndPoint;
uint32              GPDSecFrameCounter;
uint8               GPDCmmdID;
uint32              MIC;
uint8               GPDasduLength;
uint8               GPDasdu[1];         //This is a place holder for the buffer, the length depends on GPDasduLength
}gp_DataInd_t;




typedef struct
{
uint8        AppID;
union
  {
    uint32       SrcID;
    uint8        GPDExtAddr[8];
  }GPDId;
}gpd_ID_t;


typedef struct
{
gpEventHdr_t hdr;
_Bool         Action;
uint8        TxOptions;
gpd_ID_t     gpd_ID;
uint8        EndPoint;
uint8        GPDCmmdId;
uint8        GPEPhandle;
uint8        gpTxQueueEntryLifeTime[3];
uint8        GPDasduLength;
uint8        GPDasdu[1];         //This is a place holder for the buffer, the length depends on GPDasduLength
}gp_DataReq_t;

typedef struct
{
gpEventHdr_t   hdr;
uint32         timestamp;
ZMacDataReq_t  ZMacDataReq;
}gp_ZMacDataReq_t;

typedef struct
{
  gp_DataReq_t  *gp_DataReq;
}
gp_DataReqPending_t;


typedef struct
{
gpEventHdr_t hdr;
uint8        status;
uint8        GPEPhandle;
}gp_DataCnf_t;

typedef struct
{
gpEventHdr_t hdr;
uint8        status;
uint8        MPDUhandle;
}cgp_DataCnf_t;


typedef struct
{
uint8        GPDFSecLvl;
uint8        GPDFKeyType;
uint32       GPDSecFrameCounter;
}gp_SecData_t;




typedef struct
{
gpEventHdr_t hdr;
gpd_ID_t     gpd_ID;
uint8        EndPoint;
gp_SecData_t gp_SecData;
uint8        dGPStubHandle;
}gp_SecReq_t;



typedef struct
{
gpEventHdr_t  hdr;
uint8         Status;
uint8         dGPStubHandle;
gpd_ID_t      gpd_ID;
uint8         EndPoint;
gp_SecData_t  gp_SecData;
uint8         GPDKey[16];
}gp_SecRsp_t;




/*********************************************************************
 * GLOBAL VARIABLES
 */
 
extern byte gp_TaskID;
 
/*********************************************************************
 * FUNCTION MACROS
 */
 
 

/*********************************************************************
 * FUNCTIONS
 */

/*
 * @brief This function reports the results CGP Data request being 
 *        handled by the cGP stub
 */

extern void CGP_DataCnf(uint8 Status, uint8 GPmpduHandle);

/*
 * @brief Allows dGP or dLPED stub send GPDF to GPD or LPED
 */

extern ZStatus_t CGP_DataReq(uint8 TxOptions, zAddrType_t *SrcAddr, uint16 SrcPanID,  zAddrType_t *dstAddr, uint16 DstPanID, uint8 mpdu_len, uint8*  mpdu, uint8 mpduHandle,uint32 timestamp);


/*
 * @brief       Funtion to parse GPDF to pass to dedicated Stub (dGP)
 */  
extern void cGP_processMCPSDataInd(macMcpsDataInd_t *pData);

/*
 * @brief Sends GPDF in the calculated window to the GPD. 
 */
extern void gp_SendScheduledMacDataReq(void);







 
 
 
 
 
 
 
 
 
 
#line 53 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl_green_power.h"

 /*********************************************************************
 * MACROS
 */ 




#line 75 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl_green_power.h"
  


  
#line 94 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl_green_power.h"
   
// Bit shift


// Create a bitmask of specified len.


// Create a bitfield mask of length starting at start bit.


// Prepare a bitmask for insertion or combining.


// Extract a bitfield of length starting at start bit from y.


// Extract a bitfield of length starting at start bit from y.


// Insert a new bitfield value x into y.


      
// Insert a new bitfield value x into y.


      
      























      








































/*******************************************************************************
* Proxy Table Entry Options Bitfield managment
*
* Bits: 0..2              3               4               5              6         
* ApplicationID      EntryActive      EntryValid      Sequence      Lightweight    
*                                                      number       Unicast GPS    
*                                                   capabilities
*
*             7               8                  9                10             11       
*          Derived      Commissioned       FirstToForward      InRange       GPD Fixed    
*         Group GPS       Group GPS
*                            
*                           12                     13                14                  15
*                   HasAllUnicastRoutes      AssignedAlias      SecurityUse      Options Extension
*
********************************************************************************/     





























































/*******************************************************************************
* Proxy Table Entry Security Options Bitfield managment
*
* Bits: 0..1             3..4                5..7       
* SecurityLevel      SecurityKeyType       Reserved  
*
********************************************************************************/     






// GP notification options 
















// GP commissioning notification options 
























/*********************************************************************
 * CONSTANTS
 */

// For internal EP's simple descriptor



  
/********************************/
/*** Green Power Cluster Attributes ***/
/********************************/
#line 338 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl_green_power.h"

#line 347 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl_green_power.h"

// A.3.3.3 Attributes shared by client and server 



   
/*** Maximum number of Proxy Table entries supported by this device ***/

   
/*** Number of full unicast GP Notification retries on lack of GP 
     Notification Response ***/


/*** Time in ms between full unicast GP Notification retries on 
     lack of GP Notification Response ***/

   
/*** The frequency of sink rediscovery for inactive Proxy
     Table entries ***/  

   
/*** A list holding information about blocked GPD IDs ***/ 

   
/*** The optional GP functionality supported by this proxy ***/ 
/*** Format of the gppFunctionality attribute ***/
/***********************************************************************************************************
                            Indication Functionality Basic Proxy
-------------------------------------------------------------------------------------------------------------
b0    ||  GP feature                                                                              ||    0b1
b1    ||  Direct communication (reception of GPDF via GP stub)                                    ||    0b1
b2    ||  Derived groupcast communication                                                         ||    0b1
b3    ||  Pre-commissioned groupcast communication                                                ||    0b1
b4    ||  Full unicast communication                                                              ||    0b0
b5    ||  Lightweight unicast communication                                                       ||    0b1
b6    ||  Reserved                                                                                ||    0b0
b7    ||  Bidirectional operation                                                                 ||    0b0
b8    ||  Proxy Table maintenance (active and passive, for GPD mobility and GPP robustness)       ||    0b0
b9    ||  Reserved                                                                                ||    0b0
b10   ||  GP commissioning                                                                        ||    0b1
b11   ||  CT-based commissioning                                                                  ||    0b1
b12   ||  Maintenance of GPD (deliver channel/key during operation)                               ||    0b0
b13   ||  gpdSecurityLevel = 0b00                                                                 ||    0b1
b14   ||  Deprecated: gpdSecurityLevel = 0b01                                                     ||    0b0
b15   ||  gpdSecurityLevel = 0b10                                                                 ||    0b1
b16   ||  gpdSecurityLevel = 0b11                                                                 ||    0b1
b17   ||  Reserved                                                                                ||    0b0
b18   ||  Reserved                                                                                ||    0b0
b19   ||  GPD IEEE address                                                                        ||    0b1
      ||  b20 – b23 Reserved                                                                      ||    0b0
************************************************************************************************************/


/*** The optional GP functionality supported by this proxy that
     is active ***/


  




// A.3.4.2.2.2.1 Options parameter
#line 424 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl_green_power.h"

// A.3.4.2.2.2.4 Security-related parameters


  
// A.3.4.2.2.2.8 Extended Options parameter



/******************************/
/*** Green Power Cluster Commands ***/
/******************************/
#line 446 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl_green_power.h"
  
  
#line 455 "F:\\Workspace\\zstack_iar_zf\\Components\\stack\\zcl\\zcl_green_power.h"



/*************************************************************
* Proxy Table Entry Options Bitfield
**************************************************************/
// Application ID bitfied



// Entry Active Bit



// Entry Valid Bit


   
// GPD MAC sequence capablities



// Lightweight Unicast GPS Bit



// Derived Group GPS Bit



// Commissioned Group GPS Bit



// FirstToForward Bit



// InRange Bit



// GPD Fixed Bit



// HasAllUnicastRoutes Bit



// Assigned Alias


       
// SecurityUse Bit



// Options Extension Bit



/*************************************************************
* Proxy Table Entry Options Bitfield
**************************************************************/






/*************************************************************
* Pairing bit fields
**************************************************************/
// Application ID bitfied


// Values



// Request type bitfied


// Values



// Add Sink bitfield


// Values


       
// Remove GPD bitfield


// Values   



// Communication Mode bitfield


// Values





// GPD Fixed



// GPD MAC sequence capablities



// Security Level



// Security Key Type



// GPD Security Frame Counter Present



// GPD Security Key Present



// GPD Assigned Alias Present



// GPD Forwarding Radius Present



/*************************************************************
* Security Related Parameters
**************************************************************/
// Security Level



// Security Key Type


       
/*************************************************************
* Gp Notification options bit field
**************************************************************/









// Security Level



// Security Key Type















/*************************************************************
* Gp Commissioning Notification options bit field
**************************************************************/

// Security Level



// Security Key Type












/*********************************************************************
 * TYPEDEFS
 */

typedef struct gpNotificationMsg
{
  afAddrType_t                 addr;
  uint8                        secNum;
  uint8*                       pMsg;
  struct gpNotificationMsg*    pNext;
}gpNotificationMsg_t;

typedef struct gpCmdPayloadMsg
{
  uint8                        secNum;
  uint8                        lenght;
  uint8*                       pMsg;
  struct gpCmdPayloadMsg*      pNext;
}gpCmdPayloadMsg_t;

// Format of entries in the Proxy Table attribute
typedef struct
{
  uint16         options;
  uint32         gpdId;
  uint8          endPoint;
  uint16         gpdAssignedAlias;
  uint8          securityOptions;
  uint32         gpdSecurityFramecounter;
  uint8          gpdKey[16];
  uint8         *pLightweightSinkAddressList;
  uint8         *pSinkGroupList;
  uint8          groupcastRadius;
  uint8          SearchCounter;
  uint16         ExtendedOptions;
  uint8         *pFullUnicastSinkAddressList;
} ProxyTableEntryFormat_t;

// The format of entries in the gppBlockedGPDID attribute
typedef struct
{
  uint16         options;
  uint32         gpdId;
  uint8          endPoint;
  uint8          sequenceNumber;
  uint8          SearchCounter;
} GppBlockedGPDIDFormat_t;


/*** Structures used for callback functions ***/
typedef struct
{
  uint8          options;
  uint8         *pData;
} zclGpNotificationResponse_t;

typedef struct
{
  afAddrType_t  *srcAddr; // requestor's address
  uint8         options[3];
  uint8         *pData;
} zclGpPairing_t;

typedef struct
{
  uint16         srcAddr;
  uint8          options;
  uint8         *pData;
} zclGpProxyCommissioningMode_t;

typedef struct
{
  uint16         dstAddr;
  uint8          options;
  uint16         tempMasterShortAddr;
  uint8          tempMasterTxChannel;
  uint8         *pData;
} zclGpResponse_t;

typedef struct
{
  uint8          status;
  uint8          options;
  uint8          totalNumberOfEntries;
  uint8          startIndex;
  uint8          entriesCount;
  uint8         *pTranslationTableList;
} zclGpTranslationTableResponse_t;

typedef struct
{
  afAddrType_t *srcAddr; // requestor's address
  uint8        options;
  uint8        *pData;
} zclGpProxyTableRequest_t;

typedef struct
{
  uint8          status;
  uint8          tableEntriesTotal;
  uint8          startIndex;
  uint8          entriesCount;
  uint8         *proxyTableEntry;
} zclGpProxyTableResponse_t;

typedef struct
{
  uint32 options;
  uint32 gpdId;
  uint8  gpdIEEE[8];
  uint8  ep;
  uint8  sinkIEEE[8];
  uint16 sinkNwkAddr;
  uint16 sinkGroupID;
  uint8  deviceId;
  uint32 gpdSecCounter;
  uint8  gpdKey[16];
  uint16 assignedAlias;
  uint8  forwardingRadius;
} gpPairingCmd_t;

typedef struct
{
  uint8 options;
  uint32 gpdId;
  uint8  gpdIEEE[8];
  uint8  ep;
  uint8  index;
} gpProxyTableReqCmd_t;

typedef struct
{
  uint16 options;
  uint32 gpdId;
  uint8  gpdIEEE[8];
  uint8  ep;
  uint32 gpdSecCounter;
  uint8  cmdId;
  uint8  payloadLen;
  uint8  *cmdPayload;
  uint16 gppShortAddr;
  uint8  gppGpdLink;
} gpNotificationCmd_t;

typedef struct
{
  uint16 options;
  uint32 gpdId;
  uint8  gpdIEEE[8];
  uint8  ep;
  uint32 gpdSecCounter;
  uint8  cmdId;
  uint8  payloadLen;
  uint8  *cmdPayload;
  uint16 gppShortAddr;
  uint8 gppGpdLink;
  uint32 mic;
} gpCommissioningNotificationCmd_t;

// From sink to a proxy to acknowledge GP Notification received in full unicast mode
typedef void (*zclGCB_GP_Notification_Response_t)( zclGpNotificationResponse_t *pCmd );

// From sink to proxies to (de)register for tunneling service or to remove GPD from the network
typedef void (*zclGCB_GP_Pairing_t)( zclGpPairing_t *pCmd );

// From sink to proxies in the whole network to indicate commissioning mode
typedef void (*zclGCB_GP_Proxy_Commissioning_Mode_t)( zclGpProxyCommissioningMode_t *pCmd );

// From sink to selected proxies, to provide data to be transmitted to Rx-capable GPD
typedef void (*zclGCB_GP_Response_t)( zclGpResponse_t *pCmd );

// To receive information on requested selected Sink Table entries, by index or by GPD ID
typedef ZStatus_t (*zclGCB_GP_Translation_Table_Response_t)( zclGpTranslationTableResponse_t *pCmd );

// To request selected Proxy Table entries, by index or by GPD ID
typedef void (*zclGCB_GP_Proxy_Table_Request_t)( zclGpProxyTableRequest_t *pRsp );

// Register Callbacks table entry - enter function pointers for callbacks that
// the application would like to receive
typedef struct
{
  zclGCB_GP_Pairing_t                  pfnGpPairingCmd;
  zclGCB_GP_Proxy_Table_Request_t      pfnGpProxyTableReqCmd;
  zclGCB_GP_Proxy_Commissioning_Mode_t pfnGpProxyCommissioningModeCmd;
  zclGCB_GP_Response_t                 pfnGpResponseCommand;
} zclGp_AppCallbacks_t;


/*********************************************************************
 * FUNCTION MACROS
 */

/*********************************************************************
 * FUNCTIONS
 */

/*
 * Register for callbacks from this cluster library
 */
extern ZStatus_t zclGp_RegisterCmdCallbacks( uint8 endpoint, zclGp_AppCallbacks_t *callbacks );

/*
 * Send GP Notification command from proxy to sink to tunnel GP frame. 
 */
extern ZStatus_t zclGp_Notification( afAddrType_t *dstAddr,
                                     uint16 options, uint8 *pCmd, uint8 seqNum );

/*
 * Send GP Pairing Search command from proxy to the sinks in entire network to 
 * get pairing indication related to GPD for Proxy Table update
 */
extern ZStatus_t zclGp_PairingSearch( afAddrType_t *dstAddr,
                                      uint16 options, uint8 *pCmd, uint8 seqNum );

/*
 * Send GP Tunneling Stop command from proxy to neighbor proxies to indicate 
 * GP Notification sent in full unicast mode
 */
extern ZStatus_t zclGp_TunnelingStop( afAddrType_t *dstAddr,
                                      uint8 options, uint8 *pCmd, uint8 seqNum );

/*
 * Send GP Commissioning Notification command from proxy to sink to tunnel 
 * GPD commissioning data.
 */
extern ZStatus_t zclGp_CommissioningNotification( afAddrType_t *dstAddr,
                                      uint16 options, uint8 *pCmd, uint8 seqNum );

/*
 * Send GP Sink Commissioning Mode command to enable commissioning mode of the 
 * sink, over the air
 */
extern ZStatus_t zclGp_SinkCommissioningMode( afAddrType_t *dstAddr, uint8 options, 
                                      uint16 gmpAddress, uint8 sinkEp, uint8 seqNum );

/*
 * Send GP Translation Table Update command to configure GPD Command Translation Table
 */
extern ZStatus_t zclGp_TranslationTableUpdate( afAddrType_t *dstAddr,
                                      uint16 options, uint8 *pCmd, uint8 seqNum );

/*
 * Send GP Translation Table Request command to provide GPD Command Translation 
 * Table content
 */
extern ZStatus_t zclGp_TranslationTableRequest( afAddrType_t *dstAddr,
                                      uint16 options, uint8 index, uint8 seqNum );

/*
 * Send GP Pairing Configuration command to configure Sink Table  
 */
extern ZStatus_t zclGp_PairingConfiguration( afAddrType_t *dstAddr, uint8 actions,
                                      uint16 options, uint8 *pCmd, uint8 seqNum );

/*
 * Send GP Sink Table Request command to read out selected Sink Table entries, 
 * by index or by GPD ID 
 */
extern ZStatus_t zclGp_SinkTableRequest( afAddrType_t *dstAddr,
                                      uint8 options, uint8 *pCmd, uint8 seqNum );

/*
 * Send GP Sink Table Request command to receive information on requested selected 
 * Proxy Table entries, by index or by GPD ID 
 */
extern ZStatus_t zclGp_SendGpProxyTableResponse( afAddrType_t *dstAddr, zclGpProxyTableResponse_t *rsp, 
                                          uint8 seqNum );

/*
 * @brief   Send the Green Power Notification Command to a device
 */
extern ZStatus_t zclGp_SendGpNotificationCommand( gpNotificationCmd_t *cmd, uint8 secNum );

/*
 * @brief   Send the Green Power Commissioning Notification Command to a device
 */
extern ZStatus_t zclGp_SendGpCommissioningNotificationCommand( gpCommissioningNotificationCmd_t *pCmd );

/*
 * @brief   Create Notification Msg List for paired sinks if empty
 */
void gp_CreateNotificationMsgList( gpNotificationMsg_t **pHead );

/*
 * @brief   Create Notification Msg List for paired sinks if empty
 */
void gp_CreateCmdPayloadMsgList( gpCmdPayloadMsg_t **pHead );

/*
 * @brief   Add node to Notification Msg list
 */
gpNotificationMsg_t* gp_AddNotificationMsgNode( gpNotificationMsg_t **pHead, gpCmdPayloadMsg_t *pMsg );

/*
 * @brief   Add node to Notification Msg list
 */
gpCmdPayloadMsg_t* gp_AddCmdPayloadMsgNode( gpCmdPayloadMsg_t **pHead, uint8* pBuf, uint8 len );

/*
 * @brief   Returns head pointer for  finding and binding respondent list
 */
gpNotificationMsg_t* gp_GetHeadNotificationMsg(void);

/*
 * @brief   Returns head pointer for  finding and binding respondent list
 */
gpNotificationMsg_t** gp_GetPHeadNotification(void);

/*
 * @brief   Returns head pointer for  finding and binding respondent list
 */
gpCmdPayloadMsg_t* gp_GetHeadCmdPayloadMsg(void);

/*
 * @brief   Returns head pointer for  finding and binding respondent list
 */
gpCmdPayloadMsg_t** gp_GetPHeadCmdPayload(void);

/*
 * @brief   This function free reserved memory for respondent list
 */
void gp_NotificationMsgClean( gpNotificationMsg_t **pHead );

/*
 * @brief   This function free reserved memory for respondent list
 */
void gp_CmdPayloadMsgClean( gpCmdPayloadMsg_t **pHead );

 /*
 * @brief   General function to get proxy table entry by NV index     
 */
uint8 gp_getProxyTableByIndex( uint16 nvIndex, uint8 *pEntry );

/*
 * @brief   General function to get proxy table entry by gpd_ID (GP Src ID or Extended Adddress)    
 */
uint8 gp_getProxyTableByGpId(gpd_ID_t *gpd_ID, uint8 *pEntry, uint16* NvProxyTableIndex);

/*
 * @brief   This function removes data of the given entry
 */
void gp_ResetProxyBasicTblEntry( uint8* entry );

/*********************************************************************
*********************************************************************/





#line 59 "F:\\Workspace\\zigbfuzz\\depenInfer/zcl.c"

#line 1 "F:\\Workspace\\frama-c\\frama-c-master\\share\\libc\\__fc_builtin.h"
/**************************************************************************/
/*                                                                        */
/*  This file is part of Frama-C.                                         */
/*                                                                        */
/*  Copyright (C) 2007-2022                                               */
/*    CEA (Commissariat Ã  l'Ã©nergie atomique et aux Ã©nergies              */
/*         alternatives)                                                  */
/*                                                                        */
/*  you can redistribute it and/or modify it under the terms of the GNU   */
/*  Lesser General Public License as published by the Free Software       */
/*  Foundation, version 2.1.                                              */
/*                                                                        */
/*  It is distributed in the hope that it will be useful,                 */
/*  but WITHOUT ANY WARRANTY; without even the implied warranty of        */
/*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         */
/*  GNU Lesser General Public License for more details.                   */
/*                                                                        */
/*  See the GNU Lesser General Public License version 2.1                 */
/*  for more details (enclosed in the file licenses/LGPLv2.1).            */
/*                                                                        */
/**************************************************************************/

#line 1 "F:\\Workspace\\frama-c\\frama-c-master\\share\\libc\\features.h"
/**************************************************************************/
/*                                                                        */
/*  This file is part of Frama-C.                                         */
/*                                                                        */
/*  Copyright (C) 2007-2022                                               */
/*    CEA (Commissariat Ã  l'Ã©nergie atomique et aux Ã©nergies              */
/*         alternatives)                                                  */
/*                                                                        */
/*  you can redistribute it and/or modify it under the terms of the GNU   */
/*  Lesser General Public License as published by the Free Software       */
/*  Foundation, version 2.1.                                              */
/*                                                                        */
/*  It is distributed in the hope that it will be useful,                 */
/*  but WITHOUT ANY WARRANTY; without even the implied warranty of        */
/*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         */
/*  GNU Lesser General Public License for more details.                   */
/*                                                                        */
/*  See the GNU Lesser General Public License version 2.1                 */
/*  for more details (enclosed in the file licenses/LGPLv2.1).            */
/*                                                                        */
/**************************************************************************/




// *** Definitions to improve compatibility with GCC-specific built-ins
// and GNU-based code ***

#line 36 "F:\\Workspace\\frama-c\\frama-c-master\\share\\libc\\features.h"

#line 44 "F:\\Workspace\\frama-c\\frama-c-master\\share\\libc\\features.h"






#line 62 "F:\\Workspace\\frama-c\\frama-c-master\\share\\libc\\features.h"

// Frama-C does not support GCC's __builtin_object_size.
// To improve compatibility with some codebases,
// we define it anyway, but it always returns -1, as if
// the compiler were unable to statically determine
// the object size (we only consider the cases where type
// is either 0 or 1).
// Note that for some built-ins, we force them to our definition,
// while others we leave unmodified if they exist
#line 77 "F:\\Workspace\\frama-c\\frama-c-master\\share\\libc\\features.h"

#line 84 "F:\\Workspace\\frama-c\\frama-c-master\\share\\libc\\features.h"




#line 106 "F:\\Workspace\\frama-c\\frama-c-master\\share\\libc\\features.h"












// When linking code including Frama-C's libc, we avoid adding 'extern'
// to some variable declarations. In this case, __FC_EXTERN is defined to
// the empty string. Otherwise, define it to 'extern'.




// C11 Â§6.10.8.3 Conditional feature macros: Frama-C does not support complex.h




/* end __FC_FEATURES_H */
#line 26 "F:\\Workspace\\frama-c\\frama-c-master\\share\\libc\\__fc_builtin.h"

#line 1 "F:\\Workspace\\frama-c\\frama-c-master\\share\\libc\\__fc_define_size_t.h"
/**************************************************************************/
/*                                                                        */
/*  This file is part of Frama-C.                                         */
/*                                                                        */
/*  Copyright (C) 2007-2022                                               */
/*    CEA (Commissariat Ã  l'Ã©nergie atomique et aux Ã©nergies              */
/*         alternatives)                                                  */
/*                                                                        */
/*  you can redistribute it and/or modify it under the terms of the GNU   */
/*  Lesser General Public License as published by the Free Software       */
/*  Foundation, version 2.1.                                              */
/*                                                                        */
/*  It is distributed in the hope that it will be useful,                 */
/*  but WITHOUT ANY WARRANTY; without even the implied warranty of        */
/*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         */
/*  GNU Lesser General Public License for more details.                   */
/*                                                                        */
/*  See the GNU Lesser General Public License version 2.1                 */
/*  for more details (enclosed in the file licenses/LGPLv2.1).            */
/*                                                                        */
/**************************************************************************/







typedef unsigned int size_t;


#line 28 "F:\\Workspace\\frama-c\\frama-c-master\\share\\libc\\__fc_builtin.h"



extern volatile int Frama_C_entropy_source __attribute__((unused));

/*@ requires valid_p: \valid(p + (0 .. l-1));
    assigns p[0 .. l-1] \from Frama_C_entropy_source;
    assigns Frama_C_entropy_source \from Frama_C_entropy_source;
    ensures initialization: \initialized(p + (0 .. l-1));
*/
extern void Frama_C_make_unknown(char *p, size_t l);

/*@ assigns \result \from a, b, Frama_C_entropy_source;
    assigns Frama_C_entropy_source \from Frama_C_entropy_source;
    ensures result_a_or_b: \result == a || \result == b ;
 */
extern int Frama_C_nondet(int a, int b);

/*@ assigns \result \from a, b, Frama_C_entropy_source;
    assigns Frama_C_entropy_source \from Frama_C_entropy_source;
    ensures result_a_or_b: \result == a || \result == b ;
 */
extern void *Frama_C_nondet_ptr(void *a, void *b);

/*@ requires order: min <= max;
    assigns \result \from min, max, Frama_C_entropy_source;
    assigns Frama_C_entropy_source \from Frama_C_entropy_source;
    ensures result_bounded: min <= \result <= max ;
 */
extern int Frama_C_interval(int min, int max);

/*@ requires order: min <= max;
    assigns \result \from min, max, Frama_C_entropy_source;
    assigns Frama_C_entropy_source \from Frama_C_entropy_source;
    ensures result_bounded: min <= \result <= max ;
 */
extern int Frama_C_interval_split(int min, int max);

/*@ requires order: min <= max;
    assigns \result \from min, max, Frama_C_entropy_source;
    assigns Frama_C_entropy_source \from Frama_C_entropy_source;
    ensures result_bounded: min <= \result <= max ;
 */
extern unsigned char Frama_C_unsigned_char_interval
  (unsigned char min, unsigned char max);

/*@ requires order: min <= max;
    assigns \result \from min, max, Frama_C_entropy_source;
    assigns Frama_C_entropy_source \from Frama_C_entropy_source;
    ensures result_bounded: min <= \result <= max ;
 */
extern char Frama_C_char_interval(char min, char max);

/*@ requires order: min <= max;
    assigns \result \from min, max, Frama_C_entropy_source;
    assigns Frama_C_entropy_source \from Frama_C_entropy_source;
    ensures result_bounded: min <= \result <= max ;
 */
extern unsigned short Frama_C_unsigned_short_interval(unsigned short min, unsigned short max);

/*@ requires order: min <= max;
    assigns \result \from min, max, Frama_C_entropy_source;
    assigns Frama_C_entropy_source \from Frama_C_entropy_source;
    ensures result_bounded: min <= \result <= max ;
 */
extern short Frama_C_short_interval(short min, short max);


/*@ requires order: min <= max;
    assigns \result \from min, max, Frama_C_entropy_source;
    assigns Frama_C_entropy_source \from Frama_C_entropy_source;
    ensures result_bounded: min <= \result <= max ;
 */
extern unsigned int Frama_C_unsigned_int_interval(unsigned int min, unsigned int max);

/*@ requires order: min <= max;
    assigns \result \from min, max, Frama_C_entropy_source;
    assigns Frama_C_entropy_source \from Frama_C_entropy_source;
    ensures result_bounded: min <= \result <= max ;
 */
extern int Frama_C_int_interval(int min, int max);


/*@ requires order: min <= max;
    assigns \result \from min, max, Frama_C_entropy_source;
    assigns Frama_C_entropy_source \from Frama_C_entropy_source;
    ensures result_bounded: min <= \result <= max ;
 */
extern unsigned long Frama_C_unsigned_long_interval
     (unsigned long min, unsigned long max);

/*@ requires order: min <= max;
    assigns \result \from min, max, Frama_C_entropy_source;
    assigns Frama_C_entropy_source \from Frama_C_entropy_source;
    ensures result_bounded: min <= \result <= max ;
 */
extern long Frama_C_long_interval(long min, long max);


/*@ requires order: min <= max;
    assigns \result \from min, max, Frama_C_entropy_source;
    assigns Frama_C_entropy_source \from Frama_C_entropy_source;
    ensures result_bounded: min <= \result <= max ;
 */
extern unsigned long long Frama_C_unsigned_long_long_interval
     (unsigned long long min, unsigned long long max);

/*@ requires order: min <= max;
    assigns \result \from min, max, Frama_C_entropy_source;
    assigns Frama_C_entropy_source \from Frama_C_entropy_source;
    ensures result_bounded: min <= \result <= max ;
 */
extern long long Frama_C_long_long_interval(long long min, long long max);


/*@ requires order: min <= max;
    assigns \result \from min, max, Frama_C_entropy_source;
    assigns Frama_C_entropy_source \from Frama_C_entropy_source;
    ensures result_bounded: min <= \result <= max ;
 */
extern size_t Frama_C_size_t_interval(size_t min, size_t max);


/*@ requires finite: \is_finite(min) && \is_finite(max);
    requires order: min <= max;
    assigns \result \from min, max, Frama_C_entropy_source;
    assigns Frama_C_entropy_source \from Frama_C_entropy_source;
    ensures result_bounded: \is_finite(\result) && min <= \result <= max;
 */
extern float Frama_C_float_interval(float min, float max);

/*@ requires finite: \is_finite(min) && \is_finite(max);
    requires order: min <= max;
    assigns \result \from min, max, Frama_C_entropy_source;
    assigns Frama_C_entropy_source \from Frama_C_entropy_source;
    ensures result_bounded: \is_finite(\result) && min <= \result <= max;
 */
extern double Frama_C_double_interval(double min, double max);

/*@ requires finite: \is_finite(min) && \is_finite(max);
    requires order: min <= max;
    assigns \result \from min, max, Frama_C_entropy_source;
    assigns Frama_C_entropy_source \from Frama_C_entropy_source;
    ensures result_bounded: \is_finite(\result) && min <= \result <= max;
 */
extern double Frama_C_real_interval_as_double(double min, double max);

/*@ // Signals an error;
  terminates \false;
  assigns \nothing;
  ensures never_terminates: \false;
*/
extern void Frama_C_abort(void) __attribute__ ((__noreturn__));

/*@ assigns \result \from p; */
extern size_t Frama_C_offset(const void* p);

extern void *Frama_C_malloc_fresh(size_t size);

//@ assigns \result \from i;
extern long long Frama_C_abstract_cardinal(long long i);
//@ assigns \result \from i;
extern long long Frama_C_abstract_max(long long i);
//@ assigns \result \from i;
extern long long Frama_C_abstract_min(long long i);




#line 61 "F:\\Workspace\\zigbfuzz\\depenInfer/zcl.c"
#line 1 "F:\\Workspace\\zigbfuzz\\depenInfer\\config.h"

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



const cId_t zclTest_OutClusterList[] =
{
  0x0000,
  0x0007,
};





zclOptionRec_t zclBasic_Test_Options[1] =
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
  (sizeof(zclTest_InClusterList) / sizeof(zclTest_InClusterList[0])),         		//  byte  AppNumInClusters;
  (cId_t *)zclTest_InClusterList, 		//  byte *pAppInClusterList;
  (sizeof(zclTest_OutClusterList) / sizeof(zclTest_OutClusterList[0])),        		//  byte  AppNumInClusters;
  (cId_t *)zclTest_OutClusterList 		//  byte *pAppInClusterList;
};

endPointDesc_t zclTest_epDesc = {
    .endPoint = 8,
    .task_id = (uint8 *)6,
    .simpleDesc = &zclTest_SimpleDesc
};

// Used to assign to global variable attrList for zclFindAttrRecsList
const zclAttrRec_t zclTest_Attrs_All[] =
{

  // *** Identify Cluster Attribute ***
  {
    0x0003,
    { // Attribute record
      0x0000,
      0x21,
      (0x01 | 0x02),
      (void *)&zclTest_IdentifyTime
    }
  },

  // *** General Basic Cluster Attributes ***
  {
    0x0000,             
    {  // Attribute record
      0x0003,            
      0x20,                 
      0x01,                
      (void *)&zclTest_HWRevision 
    }
  },
  {
    0x0000,
    { // Attribute record
      0x0000,
      0x20,
      0x01,
      (void *)&zclTest_ZCLVersion
    }
  },
  {
    0x0000,
    { // Attribute record
      0x0004,
      0x42,
      0x01,
      (void *)zclTest_ManufacturerName
    }
  },
  {
    0x0000,
    { // Attribute record
      0x0005,
      0x42,
      0x01,
      (void *)zclTest_ModelId
    }
  },
  {
    0x0000,
    { // Attribute record
      0x0006,
      0x42,
      0x10,
      (void *)zclTest_DateCode
    }
  },
  {
    0x0000,
    { // Attribute record
      0x0007,
      0x30,
      0x01,
      (void *)&zclTest_PowerSource
    }
  },
  {
    0x0000,
    { // Attribute record
      0x0010,
      0x42,
      (0x01 | 0x02),
      0
    }
  },
  {
    0x0000,
    { // Attribute record
      0x0011,
      0x30,
      (0x01 | 0x02),
      (void *)&zclTest_PhysicalEnvironment
    }
  },
  {
    0x0000,
    { // Attribute record
      0x0012,
      0x10,
      (0x01 | 0x02),
      (void *)&zclTest_DeviceEnable
    }
  },
  {
    0x0000,
    {  // Attribute record
      0xFFFD,
      0x21,
      0x01,
      (void *)&zclTest_clusterRevision_all
    }
  },
  {
    0x0003,
    {  // Attribute record
      0xFFFD,
      0x21,
      0x01,
      (void *)&zclTest_clusterRevision_all
    }
  },
};
const zclAttrRecsList zclTest_AttrList = {
	.endpoint = 8,
	.attrs = zclTest_Attrs_All,
	.numAttributes = sizeof(zclTest_Attrs_All) / sizeof(zclTest_Attrs_All[0]),
	.next = (zclAttrRecsList *)0,
};

// Used to assign to global variable gpCmdList for zclFindCmdRecsList
#line 62 "F:\\Workspace\\zigbfuzz\\depenInfer/zcl.c"

   
/*********************************************************************
 * MACROS
 */
/*** Frame Control ***/





/*** Attribute Access Control ***/
#line 80 "F:\\Workspace\\zigbfuzz\\depenInfer/zcl.c"








// Commands that have corresponding responses (ZCL_CMD_WRITE_NO_RSP, does not have response, but must not send default response)
#line 101 "F:\\Workspace\\zigbfuzz\\depenInfer/zcl.c"

/*********************************************************************
 * CONSTANTS
 */

/*********************************************************************
 * TYPEDEFS
 */
typedef struct zclLibPlugin
{
  struct zclLibPlugin *next;
  uint16              startClusterID;    // starting cluster ID
  uint16              endClusterID;      // ending cluster ID
  zclInHdlr_t         pfnIncomingHdlr;    // function to handle incoming message
} zclLibPlugin_t;

// Command record list
typedef struct zclCmdRecsList
{
  struct zclCmdRecsList *pNext;
  uint8                 endpoint;
  uint8                 numCommands;
  const zclCommandRec_t *pCmdRecs;
} zclCmdRecsList_t;


// Cluster option list item
typedef struct zclClusterOptionList
{
  struct zclClusterOptionList *next;
  uint8                       endpoint;   // Used to link it into the endpoint descriptor
  uint8                       numOptions; // Number of the following records
  zclOptionRec_t              *options;   // option records
} zclClusterOptionList;

typedef void *(*zclParseInProfileCmd_t)( zclParseCmd_t *pCmd );
typedef uint8 (*zclProcessInProfileCmd_t)( zclIncoming_t *pInMsg );

typedef struct
{
  zclParseInProfileCmd_t   pfnParseInProfile;
  zclProcessInProfileCmd_t pfnProcessInProfile;
} zclCmdItems_t;


// List record for external handler for unhandled ZCL Foundation commands/rsps
typedef struct zclExternalFoundationHandlerList
{
    struct zclExternalFoundationHandlerList *next;
    uint8 zcl_ExternalTaskID;
    uint8 zcl_ExternalEndPoint;
} zclExternalFoundationHandlerList;


/*********************************************************************
 * GLOBAL VARIABLES
 */


  uint8 zcl_TaskID;


// The Application should register its attribute data validation function
zclValidateAttrData_t zcl_ValidateAttrDataCB = (zclValidateAttrData_t)0;

// ZCL Sequence number
//uint8 zcl_SeqNum = 0x00;  //Not longer used, refer to bdb_getZCLFrameCounter() in bdb_interface.h
uint8 zcl_InSeqNum = 0x00;

uint8 zcl_TransID = 0;  // This is the unique message ID (counter)

static uint8 savedZCLTransSeqNum = 0;

/*********************************************************************
 * EXTERNAL VARIABLES
 */

/*********************************************************************
 * EXTERNAL FUNCTIONS
 */

/*********************************************************************
 * LOCAL VARIABLES
 */
static zclLibPlugin_t *plugins = (zclLibPlugin_t *)0;


  static zclCmdRecsList_t *gpCmdList = (zclCmdRecsList_t *)0;


static zclAttrRecsList *attrList = (zclAttrRecsList *)0;
static zclClusterOptionList *clusterOptionList = (zclClusterOptionList *)0;

static afIncomingMSGPacket_t *rawAFMsg = (afIncomingMSGPacket_t *)0;


static zclExternalFoundationHandlerList *externalEndPointHandlerList = (zclExternalFoundationHandlerList *)0;


/*********************************************************************
 * LOCAL FUNCTIONS
 */
static uint8 *zclBuildHdr( zclFrameHdr_t *hdr, uint8 *pData );
static uint8 zclCalcHdrSize( zclFrameHdr_t *hdr );
static zclLibPlugin_t *zclFindPlugin( uint16 clusterID, uint16 profileID );


static uint8 zcl_addExternalFoundationHandler( uint8 taskId, uint8 endPointId );
static uint8 zcl_getExternalFoundationHandler( afIncomingMSGPacket_t *pInMsg );



  static zclCmdRecsList_t *zclFindCmdRecsList( uint8 endpoint );


zclAttrRecsList *zclFindAttrRecsList( uint8 endpoint );
static zclOptionRec_t *zclFindClusterOption( uint8 endpoint, uint16 clusterID );
static uint8 zclGetClusterOption( uint8 endpoint, uint16 clusterID );
static void zclSetSecurityOption( uint8 endpoint, uint16 clusterID, uint8 enable );

static uint8 zcl_DeviceOperational( uint8 srcEP, uint16 clusterID, uint8 frameType, uint8 cmd, uint16 profileID );


static zclReadWriteCB_t zclGetReadWriteCB( uint8 endpoint );
static zclAuthorizeCB_t zclGetAuthorizeCB( uint8 endpoint );



ZStatus_t zclReadAttrData( uint8 *pAttrData, zclAttrRec_t *pAttr, uint16 *pDataLen );
static uint16 zclGetAttrDataLengthUsingCB( uint8 endpoint, uint16 clusterID, uint16 attrId );
static ZStatus_t zclReadAttrDataUsingCB( uint8 endpoint, uint16 clusterId, uint16 attrId,
                                         uint8 *pAttrData, uint16 *pDataLen );
static ZStatus_t zclAuthorizeRead( uint8 endpoint, afAddrType_t *srcAddr, zclAttrRec_t *pAttr );
static void *zclParseInReadRspCmd( zclParseCmd_t *pCmd );
static uint8 zclProcessInReadCmd( zclIncoming_t *pInMsg );



static ZStatus_t zclWriteAttrData( uint8 endpoint, afAddrType_t *srcAddr,
                                   zclAttrRec_t *pAttr, zclWriteRec_t *pWriteRec );
static ZStatus_t zclWriteAttrDataUsingCB( uint8 endpoint, afAddrType_t *srcAddr,
                                          zclAttrRec_t *pAttr, uint8 *pAttrData );
static ZStatus_t zclAuthorizeWrite( uint8 endpoint, afAddrType_t *srcAddr, zclAttrRec_t *pAttr );
static void *zclParseInWriteRspCmd( zclParseCmd_t *pCmd );
static uint8 zclProcessInWriteCmd( zclIncoming_t *pInMsg );
static uint8 zclProcessInWriteUndividedCmd( zclIncoming_t *pInMsg );



static void *zclParseInConfigReportRspCmd( zclParseCmd_t *pCmd );
static void *zclParseInReadReportCfgRspCmd( zclParseCmd_t *pCmd );


static void *zclParseInDefaultRspCmd( zclParseCmd_t *pCmd );


static uint8 zclFindNextCmdRec( uint8 endpoint, uint16 clusterID, uint8 commandID, uint8 direction, uint8 *pCmdID, zclCommandRec_t *pCmd );
static uint8 zclFindNextAttrRec( uint8 endpoint, uint16 clusterID, uint8 direction, uint16 *attrId, zclAttrRec_t *pAttr );
static void *zclParseInDiscCmdsRspCmd( zclParseCmd_t *pCmd );
static void *zclParseInDiscAttrsRspCmd( zclParseCmd_t *pCmd );
static void *zclParseInDiscAttrsExtRspCmd( zclParseCmd_t *pCmd );
static uint8 zclProcessInDiscCmd( zclIncoming_t *pInMsg );
static uint8 zclProcessInDiscAttrs( zclIncoming_t *pInMsg );
static void zclProcessInDiscAttrsCmd( zclIncoming_t *pInMsg, zclDiscoverAttrsCmd_t *pDiscoverCmd, uint8 attrLenBuf );
static void zclProcessInDiscAttrsExtCmd( zclIncoming_t *pInMsg, zclDiscoverAttrsCmd_t *pDiscoverCmd, uint8 attrLenBuf );


/*********************************************************************
 * Parse Profile Command Function Table
 */

static const zclCmdItems_t zclCmdTable[] =
{

  /* ZCL_CMD_READ */                { zclParseInReadCmd,             zclProcessInReadCmd             },
  /* ZCL_CMD_READ_RSP */            { zclParseInReadRspCmd,          zcl_HandleExternal              },






  /* ZCL_CMD_WRITE */               { zclParseInWriteCmd,            zclProcessInWriteCmd            },
  /* ZCL_CMD_WRITE_UNDIVIDED */     { zclParseInWriteCmd,            zclProcessInWriteUndividedCmd   },
  /* ZCL_CMD_WRITE_RSP */           { zclParseInWriteRspCmd,         zcl_HandleExternal              },
  /* ZCL_CMD_WRITE_NO_RSP */        { zclParseInWriteCmd,            zclProcessInWriteCmd            },
#line 293 "F:\\Workspace\\zigbfuzz\\depenInfer/zcl.c"


    /* ZCL_CMD_CONFIG_REPORT */       { zclParseInConfigReportCmd,     zcl_HandleExternal              },





    /* ZCL_CMD_CONFIG_REPORT_RSP */   { zclParseInConfigReportRspCmd,  zcl_HandleExternal              },





    /* ZCL_CMD_READ_REPORT_CFG */     { zclParseInReadReportCfgCmd,    zcl_HandleExternal              },





    /* ZCL_CMD_READ_REPORT_CFG_RSP */ { zclParseInReadReportCfgRspCmd, zcl_HandleExternal              },





    /* ZCL_CMD_REPORT */              { zclParseInReportCmd,           zcl_HandleExternal              },




  /* ZCL_CMD_DEFAULT_RSP */         { zclParseInDefaultRspCmd,       zcl_HandleExternal              },


  /* ZCL_CMD_DISCOVER_ATTRS */                { zclParseInDiscAttrsCmd,         zclProcessInDiscAttrs           },
  /* ZCL_CMD_DISCOVER_ATTRS_RSP */            { zclParseInDiscAttrsRspCmd,      zcl_HandleExternal              },
  /* *not supported* READ_ATTRS_STRCT */      { 0,                           (zclProcessInProfileCmd_t)0  },
  /* *not supported* WRITE_ATTRS_STRCT */     { 0,                           (zclProcessInProfileCmd_t)0  },
  /* *not supported* WRITE_ATTRS_STRCT_RSP */ { 0,                           (zclProcessInProfileCmd_t)0  },
  /* ZCL_CMD_DISCOVER_CMDS_RECEIVED */        { zclParseInDiscCmdsCmd,          zclProcessInDiscCmd             },
  /* ZCL_CMD_DISCOVER_CMDS_RECEIVED_RSP */    { zclParseInDiscCmdsRspCmd,       zcl_HandleExternal              },
  /* ZCL_CMD_DISCOVER_CMDS_GEN */             { zclParseInDiscCmdsCmd,          zclProcessInDiscCmd             },
  /* ZCL_CMD_DISCOVER_CMDS_GEN_RSP */         { zclParseInDiscCmdsRspCmd,       zcl_HandleExternal              },
  /* ZCL_CMD_DISCOVER_ATTRS_EXT */            { zclParseInDiscAttrsCmd,         zclProcessInDiscAttrs           },
  /* ZCL_CMD_DISCOVER_ATTRS_EXT_RSP */        { zclParseInDiscAttrsExtRspCmd,   zcl_HandleExternal              },
#line 351 "F:\\Workspace\\zigbfuzz\\depenInfer/zcl.c"
};

/*********************************************************************
 * PUBLIC FUNCTIONS
 *********************************************************************/


/*********************************************************************
 * @fn          zcl_Init
 *
 * @brief       Initialization function for the zcl layer.
 *
 * @param       task_id - ZCL task id
 *
 * @return      none
 */
void zcl_Init( uint8 task_id )
{
  zcl_TaskID = task_id;
}



/*********************************************************************
 * @fn          zcl_event_loop
 *
 * @brief       Event Loop Processor for zcl.
 *
 * @param       task_id - task id
 * @param       events - event bitmap
 *
 * @return      unprocessed events
 */
uint16 zcl_event_loop( uint8 task_id, uint16 events )
{
  uint8 *msgPtr;

  (void)task_id;  // Intentionally unreferenced parameter

  if ( events & 0x8000 )
  {
    msgPtr = osal_msg_receive( zcl_TaskID );
    while ( msgPtr != 0 )
    {
      uint8 dealloc = 1;

      if ( *msgPtr == 0x1A )
      {
        zcl_ProcessMessageMSG( (afIncomingMSGPacket_t *)msgPtr );
      }
      else
      {
        uint8 taskID;
        taskID = zcl_getExternalFoundationHandler( (afIncomingMSGPacket_t *)msgPtr );

        if ( taskID != 0xFF )
        {
          // send it to another task to process.
          osal_msg_send( taskID, msgPtr );
          dealloc = 0;
        }
      }

      // Release the memory
      if ( dealloc )
      {
        osal_msg_deallocate( msgPtr );
      }

      // Next
      msgPtr = osal_msg_receive( zcl_TaskID );
    }

    // return unprocessed events
    return (events ^ 0x8000);
  }


  if ( events & 0x0020 )
  {
    gpNotificationMsg_t *gpNotification = 0;
    gpCmdPayloadMsg_t *pCmdPayloadMsgCurr = 0;
    uint8 appId;
    uint8 nwkSeqNum;
    uint16 nwkAddr;
    
    gpNotification = gp_GetHeadNotificationMsg( );
    
    if ( gpNotification == 0 )
    {
      return 0;
    }
    
    pCmdPayloadMsgCurr = ( gpCmdPayloadMsg_t* ) gpNotification->pMsg ;
    appId = ( ( (((uint16)*pCmdPayloadMsgCurr->pMsg)>>(0x00)) & ( ( 1<<(0x03) )-1 ) ) );
    
    // To save the NIB nwk sequense number and use the GP alias nwk sequence number
    // for the GP notification
    nwkSeqNum = _NIB.SequenceNum;
    _NIB.SequenceNum = pCmdPayloadMsgCurr->secNum;
    
    // To save the NIB nwk address and use the GP alias nwk address for the GP notification
    nwkAddr = _NIB.nwkDevAddress;
    
    if( appId == 0x00 )
    {
      osal_memcpy( &_NIB.nwkDevAddress,( pCmdPayloadMsgCurr->pMsg + sizeof( uint16 ) ), sizeof(uint16) );
    }
    else if( appId == 0x02 )
    {
      osal_revmemcpy( &_NIB.nwkDevAddress,(pCmdPayloadMsgCurr->pMsg + 8), sizeof(uint16) );
    }
    
    zcl_SendCommand( 0xF2, &gpNotification->addr, 0x0021,
                          0x00, 1, 0x00,
                          1, 0,  bdb_getZCLFrameCounter(), pCmdPayloadMsgCurr->lenght, pCmdPayloadMsgCurr->pMsg );
    
    // Restore the NIB nwk sequence number
    _NIB.SequenceNum = nwkSeqNum;
    
    // Restore the NIB nwk address
    _NIB.nwkDevAddress = nwkAddr;
    
    gp_NotificationMsgClean( gp_GetPHeadNotification ( ) );
    
    if ( gp_GetHeadNotificationMsg ( ) != 0 )
    {
      osal_start_timerEx( zcl_TaskID, 0x0020, 50 );
    }
  }


  // Discard unknown events
  return 0;
}



/*********************************************************************
 * @fn      zcl_registerForMsg
 *
 * @brief   The ZCL is setup to send all incoming Foundation Command/Response
 *          messages that aren't processed to one task (if a task is
 *          registered).
 *
 * @param   taskId - task Id of the Application where commands will be sent to
 *
 * @return  TRUE if task registeration successful, FALSE otherwise
 *********************************************************************/
uint8 zcl_registerForMsg( uint8 taskId )
{
  return zcl_addExternalFoundationHandler( taskId, 0xFF );
}

/*********************************************************************
 * @fn      zcl_registerForMsgExt
 *
 * @brief   This function enables a Task to register to recieve all
 *          incoming Foundation Command/Response messages, for a particular
 *          End Point, that aren't processed by ZCL.
 *
 *          NOTE: Any Task registered for a unique end point will take
 *          priority over any Task registered with the AF_BROADCAST_ENDPOINT
 *          value.  ie. If task A registers for End Point 1, task B registers
 *          for AF_BROADCAST_ENDPOINT,  commands addressed to End Point 1 will be
 *          sent to Task A and NOT Task B.
 *
 * @param   taskId - task Id of the Application where commands will be sent to
 * @param   endPointId - end point Id of interest
 *
 * @return  TRUE if task registeration successful, FALSE otherwise
 *********************************************************************/
uint8 zcl_registerForMsgExt( uint8 taskId, uint8 endPointId  )
{
  return ( zcl_addExternalFoundationHandler( taskId, endPointId  ) );
}

/*********************************************************************
 * @fn      zcl_addExternalFoundationHandler
 *
 * @brief   This function adds a record to the internal list of external
 *          handlers of unhandled incoming Foundation Command/Response messages.
 *
 * @param   taskId - task Id of the Application where commands will be sent to
 * @param   endPointId - end point Id of interest
 *
 * @return  TRUE if task registeration successful, FALSE otherwise
 *********************************************************************/
uint8 zcl_addExternalFoundationHandler( uint8 taskId, uint8 endPointId  )
{
  zclExternalFoundationHandlerList *pNewItem;
  zclExternalFoundationHandlerList *pLoop;
  zclExternalFoundationHandlerList *pLoopPrev;

  // Fill in the new endpoint registrant list
  pNewItem = osal_mem_alloc( sizeof( zclExternalFoundationHandlerList ) );
  if ( pNewItem == 0 )
  {
    return ( 0 );
  }

  pNewItem->zcl_ExternalEndPoint = endPointId;
  pNewItem->zcl_ExternalTaskID = taskId;
  pNewItem->next = 0;

  // Add to the list
  if ( externalEndPointHandlerList == 0 )
  {
    externalEndPointHandlerList = pNewItem;
  }
  else
  {
    // make sure no one else tried to register for this endpoint
    pLoop = externalEndPointHandlerList;
    pLoopPrev = externalEndPointHandlerList;

    while ( pLoop != 0 )
    {
      if ( ( pLoop->zcl_ExternalEndPoint ) == endPointId )
      {
        osal_mem_free(pNewItem);
        return ( 0 );
      }
      pLoopPrev = pLoop;
      pLoop = pLoop->next;
    }

    if ( endPointId == 0xFF )
    {
      // put new registration at the end of the list
      pLoopPrev->next = pNewItem;
      pNewItem->next = 0;
    }
    else
    {
      // put new registration at the front of the list
      zclExternalFoundationHandlerList *temp = externalEndPointHandlerList;
      externalEndPointHandlerList = pNewItem;
      pNewItem->next = temp;
    }
  }

  return ( 1 );

}

/*********************************************************************
 * @fn      zcl_getExternalFoundationHandler
 *
 * @brief   This function retrieves the Task ID of the task registered
 *          to received unhandled incoming Foundation Command/Response messages
 *          for a particular End Point ID.
 *
 * @param   pInMsg - recevied ZCL command
 *
 * @return  TASK ID of registered task.  If no task is reigistered, it returns
 *          TASK_NO_TASK.
 *********************************************************************/
static uint8 zcl_getExternalFoundationHandler( afIncomingMSGPacket_t *pInMsg )
{
  zclExternalFoundationHandlerList *pLoop;
  uint8 addressedEndPointId = pInMsg->endPoint;

  // make sure no one else tried to register for this endpoint
  pLoop = externalEndPointHandlerList;

  while ( pLoop != 0 )
  {
    if ( ( ( pLoop->zcl_ExternalEndPoint ) == addressedEndPointId ) ||
         ( ( pLoop->zcl_ExternalEndPoint ) == 0xFF ) )
    {
      return ( pLoop->zcl_ExternalTaskID );
    }
    pLoop = pLoop->next;
  }

  return ( 0xFF );
}



/*********************************************************************
 * @fn      zcl_HandleExternal
 *
 * @brief
 *
 * @param   pInMsg - incoming message to process
 *
 * @return  TRUE
 */
uint8 zcl_HandleExternal( zclIncoming_t *pInMsg )
{
  zclIncomingMsg_t *pCmd;
  uint8 taskID;

  taskID = zcl_getExternalFoundationHandler( pInMsg->msg );

  if ( taskID == 0xFF )
  {
    return ( 1 );
  }

  pCmd = (zclIncomingMsg_t *)osal_msg_allocate( sizeof ( zclIncomingMsg_t ) );
  if ( pCmd != 0 )
  {
    // fill in the message
    pCmd->hdr.event = 0x34;
    pCmd->zclHdr    = pInMsg->hdr;
    pCmd->clusterId = pInMsg->msg->clusterId;
    pCmd->srcAddr   = pInMsg->msg->srcAddr;
    pCmd->endPoint  = pInMsg->msg->endPoint;
    pCmd->attrCmd   = pInMsg->attrCmd;
    
#line 676 "F:\\Workspace\\zigbfuzz\\depenInfer/zcl.c"
    // Application will free the attrCmd buffer
    pInMsg->attrCmd = 0;

    /* send message through task message */
    osal_msg_send( taskID, (uint8 *)pCmd );
  }
  Frama_C_dump_each();
  return ( 1 );
}



/*********************************************************************
 * @fn          zcl_getRawAFMsg
 *
 * @brief       Call to get original unprocessed AF message
 *              (not parsed by ZCL).
 *
 *   NOTE:  This function can only be called during a ZCL callback function
 *          and the calling function must NOT change any data in the message.
 *
 * @param       none
 *
 * @return      pointer to original AF message, NULL if not processing
 *              AF message.
 */
afIncomingMSGPacket_t *zcl_getRawAFMsg( void )
{
  return ( rawAFMsg );
}

/*********************************************************************
 * @fn          zcl_getParsedTransSeqNum
 *
 * @brief       Call to the get the transaction sequence number from
 *              the incoming message.
 *
 *   NOTE:  This function can only be called during a ZCL callback function
 *          and the calling function must NOT change any data in the message.
 *
 * @param       none
 *
 * @return      transaction sequence number.
 */
uint8 zcl_getParsedTransSeqNum( void )
{
  return ( savedZCLTransSeqNum );
}

/*********************************************************************
 * @fn          zcl_registerPlugin
 *
 * @brief       Add a Cluster Library handler
 *
 * @param       startClusterID - starting cluster ID
 * @param       endClusterID - ending cluster ID
 * @param       pfnHdlr - function pointer to incoming message handler
 *
 * @return      ZSuccess if OK
 */
ZStatus_t zcl_registerPlugin( uint16 startClusterID,
          uint16 endClusterID, zclInHdlr_t pfnIncomingHdlr )
{
  zclLibPlugin_t *pNewItem;
  zclLibPlugin_t *pLoop;

  // Fill in the new profile list
  pNewItem = osal_mem_alloc( sizeof( zclLibPlugin_t ) );
  if ( pNewItem == 0 )
  {
    return (0x10);
  }

  // Fill in the plugin record.
  pNewItem->next = (zclLibPlugin_t *)0;
  pNewItem->startClusterID = startClusterID;
  pNewItem->endClusterID = endClusterID;
  pNewItem->pfnIncomingHdlr = pfnIncomingHdlr;

  // Find spot in list
  if (  plugins == 0 )
  {
    plugins = pNewItem;
  }
  else
  {
    // Look for end of list
    pLoop = plugins;
    while ( pLoop->next != 0 )
    {
      pLoop = pLoop->next;
    }

    // Put new item at end of list
    pLoop->next = pNewItem;
  }

  return ( 0x00 );
}


/*********************************************************************
 * @fn          zcl_registerCmdList
 *
 * @brief       Register a Command List with ZCL Foundation
 *
 * @param       endpoint - endpoint the attribute list belongs to
 * @param       newCmdList - array of command records
 *
 * @return      ZSuccess if OK
 */
ZStatus_t zcl_registerCmdList( uint8 endpoint, const uint8 cmdListSize, const zclCommandRec_t newCmdList[] )
{
  zclCmdRecsList_t *pNewItem;
  zclCmdRecsList_t *pLoop;

  // Fill in the new profile list
  pNewItem = osal_mem_alloc( sizeof( zclCmdRecsList_t ) );
  if ( pNewItem == 0 )
  {
    return (0x10);
  }

  pNewItem->pNext = (zclCmdRecsList_t *)0;
  pNewItem->endpoint = endpoint;
  pNewItem->numCommands = cmdListSize;
  pNewItem->pCmdRecs = newCmdList;

  // Find spot in list
  if ( gpCmdList == 0 )
  {
    gpCmdList = pNewItem;
  }
  else
  {
    // Look for end of list
    pLoop = gpCmdList;
    while ( pLoop->pNext != 0 )
    {
      pLoop = pLoop->pNext;
    }

    // Put new item at end of list
    pLoop->pNext = pNewItem;
  }

  return ( 0x00 );
}


/*********************************************************************
 * @fn          zcl_registerAttrList
 *
 * @brief       Register an Attribute List with ZCL Foundation
 *
 * @param       endpoint - endpoint the attribute list belongs to
 * @param       numAttr - number of attributes in list
 * @param       newAttrList - array of Attribute records.
 *                            NOTE: THE ATTRIBUTE IDs (FOR A CLUSTER) MUST BE IN
 *                            ASCENDING ORDER. OTHERWISE, THE DISCOVERY RESPONSE
 *                            COMMAND WILL NOT HAVE THE RIGHT ATTRIBUTE INFO
 *
 * @return      ZSuccess if OK
 */
ZStatus_t zcl_registerAttrList( uint8 endpoint, uint8 numAttr, const zclAttrRec_t newAttrList[] )
{
  zclAttrRecsList *pNewItem;
  zclAttrRecsList *pLoop;

  // Fill in the new profile list
  pNewItem = osal_mem_alloc( sizeof( zclAttrRecsList ) );
  if ( pNewItem == 0 )
  {
    return (0x10);
  }

  pNewItem->next = (zclAttrRecsList *)0;
  pNewItem->endpoint = endpoint;
  pNewItem->pfnReadWriteCB = 0;
  pNewItem->numAttributes = numAttr;
  pNewItem->attrs = newAttrList;

  // Find spot in list
  if ( attrList == 0 )
  {
    attrList = pNewItem;
  }
  else
  {
    // Look for end of list
    pLoop = attrList;
    while ( pLoop->next != 0 )
    {
      pLoop = pLoop->next;
    }

    // Put new item at end of list
    pLoop->next = pNewItem;
  }

  return ( 0x00 );
}

/*********************************************************************
 * @fn          zcl_registerClusterOptionList
 *
 * @brief       Register a Cluster Option List with ZCL Foundation
 *
 * @param       endpoint - endpoint the option list belongs to
 * @param       numOption - number of options in list
 * @param       optionList - array of cluster option records.
 *
 *              NOTE: This API should be called to enable 'Application
 *                    Link Key' security and/or 'APS ACK' for a specific
 *                    Cluster. The 'Application Link Key' is discarded
 *                    if security isn't enabled on the device.
 *                    The default behavior is 'Network Key' when security
 *                    is enabled and no 'APS ACK' for the ZCL messages.
 *
 * @return      ZSuccess if OK
 */
ZStatus_t zcl_registerClusterOptionList( uint8 endpoint, uint8 numOption, zclOptionRec_t optionList[] )
{
  zclClusterOptionList *pNewItem;
  zclClusterOptionList *pLoop;

  // Fill in the new profile list
  pNewItem = osal_mem_alloc( sizeof( zclClusterOptionList ) );
  if ( pNewItem == 0 )
  {
    return (0x10);
  }

  pNewItem->next = (zclClusterOptionList *)0;
  pNewItem->endpoint = endpoint;
  pNewItem->numOptions = numOption;
  pNewItem->options = optionList;

  // Find spot in list
  if ( clusterOptionList == 0 )
  {
    clusterOptionList = pNewItem;
  }
  else
  {
    // Look for end of list
    pLoop = clusterOptionList;
    while ( pLoop->next != 0 )
    {
      pLoop = pLoop->next;
    }

    // Put new item at end of list
    pLoop->next = pNewItem;
  }

  return ( 0x00 );
}

/*********************************************************************
 * @fn          zcl_registerValidateAttrData
 *
 * @brief       Add a validation function for attribute data
 *
 * @param       pfnValidateAttrData - function pointer to validate routine
 *
 * @return      ZSuccess if OK
 */
ZStatus_t zcl_registerValidateAttrData( zclValidateAttrData_t pfnValidateAttrData )
{
  zcl_ValidateAttrDataCB = pfnValidateAttrData;

  return ( 0x00 );
}

/*********************************************************************
 * @fn          zcl_registerReadWriteCB
 *
 * @brief       Register the application's callback function to read/write
 *              attribute data, and authorize read/write operation.
 *
 *              Note: The pfnReadWriteCB callback function is only required
 *                    when the attribute data format is unknown to ZCL. The
 *                    callback function gets called when the pointer 'dataPtr'
 *                    to the attribute value is NULL in the attribute database
 *                    registered with the ZCL.
 *
 *              Note: The pfnAuthorizeCB callback function is only required
 *                    when the Read/Write operation on an attribute requires
 *                    authorization (i.e., attributes with ACCESS_CONTROL_AUTH_READ
 *                    or ACCESS_CONTROL_AUTH_WRITE access permissions).
 *
 * @param       endpoint - application's endpoint
 * @param       pfnReadWriteCB - function pointer to read/write routine
 * @param       pfnAuthorizeCB - function pointer to authorize read/write operation
 *
 * @return      ZSuccess if successful. ZFailure, otherwise.
 */
ZStatus_t zcl_registerReadWriteCB( uint8 endpoint, zclReadWriteCB_t pfnReadWriteCB,
                                   zclAuthorizeCB_t pfnAuthorizeCB )
{
  zclAttrRecsList *pRec = zclFindAttrRecsList( endpoint );

  if ( pRec != 0 )
  {
    pRec->pfnReadWriteCB = pfnReadWriteCB;
    pRec->pfnAuthorizeCB = pfnAuthorizeCB;

    return ( 0x00 );
  }

  return ( 0x01 );
}

/*********************************************************************
 * @fn      zcl_DeviceOperational
 *
 * @brief   Used to see whether or not the device can send or respond
 *          to application level commands.
 *
 * @param   srcEP - source endpoint
 * @param   clusterID - cluster ID
 * @param   frameType - command type
 * @param   cmd - command ID
 *
 * @return  TRUE if device is operational, FALSE otherwise
 */
static uint8 zcl_DeviceOperational( uint8 srcEP, uint16 clusterID,
                                    uint8 frameType, uint8 cmd, uint16 profileID )
{
  zclAttrRec_t attrRec;
  uint8 deviceEnabled = 0x01; // default value

  (void)profileID;  // Intentionally unreferenced parameter

  // If the device is Disabled (DeviceEnabled attribute is set to Disabled), it
  // cannot send or respond to application level commands, other than commands
  // to read or write attributes. Note that the Identify cluster cannot be
  // disabled, and remains functional regardless of this setting.
  if ( ( (frameType) == 0x00 ) && cmd <= 0x05 )
  {
    return ( 1 );
  }

  if ( clusterID == 0x0003 )
  {
    return ( 1 );
  }

  // Is device enabled?
  if ( zclFindAttrRec( srcEP, 0x0000,
                       0x0012, &attrRec ) )
  {

    zclReadAttrData( &deviceEnabled, &attrRec, 0 );

  }
  Frama_C_dump_each();
  return ( deviceEnabled == 0x01 ? 1 : 0 );
}

/*********************************************************************
 * @fn      zcl_SendCommand
 *
 * @brief   Used to send Profile and Cluster Specific Command messages.
 *
 *          NOTE: The calling application is responsible for incrementing
 *                the Sequence Number.
 *
 * @param   srcEp - source endpoint
 * @param   destAddr - destination address
 * @param   clusterID - cluster ID
 * @param   cmd - command ID
 * @param   specific - whether the command is Cluster Specific
 * @param   direction - client/server direction of the command
 * @param   disableDefaultRsp - disable Default Response command
 * @param   manuCode - manufacturer code for proprietary extensions to a profile
 * @param   seqNumber - identification number for the transaction
 * @param   cmdFormatLen - length of the command to be sent
 * @param   cmdFormat - command to be sent
 *
 * @return  ZSuccess if OK
 */
ZStatus_t zcl_SendCommand( uint8 srcEP, afAddrType_t *destAddr,
                           uint16 clusterID, uint8 cmd, uint8 specific, uint8 direction,
                           uint8 disableDefaultRsp, uint16 manuCode, uint8 seqNum,
                           uint16 cmdFormatLen, uint8 *cmdFormat )
{
  endPointDesc_t *epDesc;
  zclFrameHdr_t hdr;
  uint8 *msgBuf;
  uint16 msgLen;
  uint8 *pBuf;
  uint8 options;
  ZStatus_t status;

  epDesc = afFindEndPointDesc( srcEP );
  //? env_var assignment;
  epDesc = &zclTest_epDesc;
  if ( epDesc == 0 )
  {
    return ( 0x02 ); // EMBEDDED RETURN
  }

#line 1085 "F:\\Workspace\\zigbfuzz\\depenInfer/zcl.c"
  {
    options = zclGetClusterOption( srcEP, clusterID );

    // The cluster might not have been defined to use security but if this message
    // is in response to another message that was using APS security this message
    // will be sent with APS security
    if ( !( options & 0x40 ) )
    {
      afIncomingMSGPacket_t *origPkt = zcl_getRawAFMsg();

      if ( ( origPkt != 0 ) && ( origPkt->SecurityUse == 1 ) )
      {
        options |= 0x40;
      }
    }
  }

  osal_memset( &hdr, 0, sizeof( zclFrameHdr_t ) );

  // Not Profile wide command (like READ, WRITE)
  if ( specific )
  {
    hdr.fc.type = 0x01;
  }
  else
  {
    hdr.fc.type = 0x00;
  }

  if ( ( epDesc->simpleDesc == 0 ) ||
       ( zcl_DeviceOperational( srcEP, clusterID, hdr.fc.type,
                                cmd, epDesc->simpleDesc->AppProfId ) == 0 ) )
  {
    return ( 0x01 ); // EMBEDDED RETURN
  }

  // Fill in the Maufacturer Code
  if ( manuCode != 0 )
  {
    hdr.fc.manuSpecific = 1;
    hdr.manuCode = manuCode;
  }

  // Set the Command Direction
  if ( direction )
  {
    hdr.fc.direction = 0x01;
  }
  else
  {
    hdr.fc.direction = 0x00;
  }

  // Set the Disable Default Response field
  if ( disableDefaultRsp )
  {
    hdr.fc.disableDefaultRsp = 1;
  }
  else
  {
    hdr.fc.disableDefaultRsp = 0;
  }

  // Fill in the Transaction Sequence Number
  hdr.transSeqNum = seqNum;

  // Fill in the command
  hdr.commandID = cmd;

  // calculate the needed buffer size
  msgLen = zclCalcHdrSize( &hdr );
  msgLen += cmdFormatLen;

  // Allocate the buffer needed
  msgBuf = osal_mem_alloc( msgLen );
  if ( msgBuf != 0 )
  {
    // Fill in the ZCL Header
    pBuf = zclBuildHdr( &hdr, msgBuf );

    // Fill in the command frame
    osal_memcpy( pBuf, cmdFormat, cmdFormatLen );

    //status = AF_DataRequest( destAddr, epDesc, clusterID, msgLen, msgBuf,
    //                         &zcl_TransID, options, AF_DEFAULT_RADIUS );
    status = 0x00;
    osal_mem_free ( msgBuf );
  }
  else
  {
    status = 0x10;
  }
  Frama_C_dump_each();
  return ( status );
}


/*********************************************************************
 * @fn      zcl_SendRead
 *
 * @brief   Send a Read command
 *
 * @param   srcEP - Application's endpoint
 * @param   dstAddr - destination address
 * @param   clusterID - cluster ID
 * @param   readCmd - read command to be sent
 * @param   direction - direction of the command
 * @param   seqNum - transaction sequence number
 *
 * @return  ZSuccess if OK
 */
ZStatus_t zcl_SendRead( uint8 srcEP, afAddrType_t *dstAddr,
                        uint16 clusterID, zclReadCmd_t *readCmd,
                        uint8 direction, uint8 disableDefaultRsp, uint8 seqNum)
{
  uint16 dataLen;
  uint8 *buf;
  uint8 *pBuf;
  ZStatus_t status;

  dataLen = readCmd->numAttr * 2; // Attribute ID

  buf = osal_mem_alloc( dataLen );
  if ( buf != 0 )
  {
    uint8 i;

    // Load the buffer - serially
    pBuf = buf;
    for (i = 0; i < readCmd->numAttr; i++)
    {
      *pBuf++ = ((readCmd->attrID[i]) & 0xFF);
      *pBuf++ = (((readCmd->attrID[i]) >> 8) & 0xFF);
    }

    status = zcl_SendCommand( srcEP, dstAddr, clusterID, 0x00, 0,
                              direction, disableDefaultRsp, 0, seqNum, dataLen, buf );
    osal_mem_free( buf );
  }
  else
  {
    status = 0x10;
  }

  return ( status );
}

/*********************************************************************
 * @fn      zcl_SendReadRsp
 *
 * @brief   Send a Read Response command.
 *
 * @param   srcEP - Application's endpoint
 * @param   dstAddr - destination address
 * @param   clusterID - cluster ID
 * @param   readRspCmd - read response command to be sent
 * @param   direction - direction of the command
 * @param   seqNum - transaction sequence number
 *
 * @return  ZSuccess if OK
 */
ZStatus_t zcl_SendReadRsp( uint8 srcEP, afAddrType_t *dstAddr,
                           uint16 clusterID, zclReadRspCmd_t *readRspCmd,
                           uint8 direction, uint8 disableDefaultRsp, uint8 seqNum )
{
  uint8 *buf;
  uint16 len = 0;
  ZStatus_t status;
  uint8 i;

  // calculate the size of the command
  for ( i = 0; i < readRspCmd->numAttr; i++ )
  {
    zclReadRspStatus_t *statusRec = &(readRspCmd->attrList[i]);

    len += 2 + 1; // Attribute ID + Status

    if ( statusRec->status == 0x00 )
    {
      len++; // Attribute Data Type length

      // Attribute Data length
      if ( statusRec->data != 0 )
      {
        len += zclGetAttrDataLength( statusRec->dataType, statusRec->data );
      }
      else
      {
        len += zclGetAttrDataLengthUsingCB( srcEP, clusterID, statusRec->attrID );
      }
    }
  }

  buf = osal_mem_alloc( len );
  if ( buf != 0 )
  {
    // Load the buffer - serially
    uint8 *pBuf = buf;

    for ( i = 0; i < readRspCmd->numAttr; i++ )
    {
      zclReadRspStatus_t *statusRec = &(readRspCmd->attrList[i]);

      *pBuf++ = ((statusRec->attrID) & 0xFF);
      *pBuf++ = (((statusRec->attrID) >> 8) & 0xFF);
      *pBuf++ = statusRec->status;

      if ( statusRec->status == 0x00 )
      {
        *pBuf++ = statusRec->dataType;

        if ( statusRec->data != 0 )
        {
          // Copy attribute data to the buffer to be sent out
          pBuf = zclSerializeData( statusRec->dataType, statusRec->data, pBuf );
        }
        else
        {
          uint16 dataLen;

          // Read attribute data directly into the buffer to be sent out
          zclReadAttrDataUsingCB( srcEP, clusterID, statusRec->attrID, pBuf, &dataLen );
          pBuf += dataLen;
        }
      }
    } // for loop

    status = zcl_SendCommand( srcEP, dstAddr, clusterID, 0x01, 0,
                              direction, disableDefaultRsp, 0, seqNum, len, buf );
    osal_mem_free( buf );
  }
  else
  {
    status = 0x10;
  }

  return ( status );
}



/*********************************************************************
 * @fn      sendWriteRequest
 *
 * @brief   Send a Write command
 *
 * @param   dstAddr - destination address
 * @param   clusterID - cluster ID
 * @param   writeCmd - write command to be sent
 * @param   cmd - ZCL_CMD_WRITE, ZCL_CMD_WRITE_UNDIVIDED or ZCL_CMD_WRITE_NO_RSP
 * @param   direction - direction of the command
 * @param   seqNum - transaction sequence number
 *
 * @return  ZSuccess if OK
 */
ZStatus_t zcl_SendWriteRequest( uint8 srcEP, afAddrType_t *dstAddr, uint16 clusterID,
                                zclWriteCmd_t *writeCmd, uint8 cmd, uint8 direction,
                                uint8 disableDefaultRsp, uint8 seqNum )
{
  uint8 *buf;
  uint16 dataLen = 0;
  ZStatus_t status;
  uint8 i;

  for ( i = 0; i < writeCmd->numAttr; i++ )
  {
    zclWriteRec_t *statusRec = &(writeCmd->attrList[i]);

    dataLen += 2 + 1; // Attribute ID + Attribute Type

    // Attribute Data
    dataLen += zclGetAttrDataLength( statusRec->dataType, statusRec->attrData );
  }

  buf = osal_mem_alloc( dataLen );
  if ( buf != 0 )
  {
    // Load the buffer - serially
    uint8 *pBuf = buf;
    for ( i = 0; i < writeCmd->numAttr; i++ )
    {
      zclWriteRec_t *statusRec = &(writeCmd->attrList[i]);

      *pBuf++ = ((statusRec->attrID) & 0xFF);
      *pBuf++ = (((statusRec->attrID) >> 8) & 0xFF);
      *pBuf++ = statusRec->dataType;

      pBuf = zclSerializeData( statusRec->dataType, statusRec->attrData, pBuf );
    }

    status = zcl_SendCommand( srcEP, dstAddr, clusterID, cmd, 0,
                              direction, disableDefaultRsp, 0, seqNum, dataLen, buf );
    osal_mem_free( buf );
  }
  else
  {
    status = 0x10;
  }

  return ( status);
}

/*********************************************************************
 * @fn      zcl_SendWriteRsp
 *
 * @brief   Send a Write Response command
 *
 * @param   dstAddr - destination address
 * @param   clusterID - cluster ID
 * @param   wrtieRspCmd - write response command to be sent
 * @param   direction - direction of the command
 * @param   seqNum - transaction sequence number
 *
 * @return  ZSuccess if OK
 */
ZStatus_t zcl_SendWriteRsp( uint8 srcEP, afAddrType_t *dstAddr,
                            uint16 clusterID, zclWriteRspCmd_t *writeRspCmd,
                            uint8 direction, uint8 disableDefaultRsp, uint8 seqNum )
{
  uint16 dataLen;
  uint8 *buf;
  ZStatus_t status;

  dataLen = writeRspCmd->numAttr * ( 1 + 2 ); // status + attribute id

  buf = osal_mem_alloc( dataLen );
  if ( buf != 0 )
  {
    // Load the buffer - serially
    uint8 i;
    uint8 *pBuf = buf;
    for ( i = 0; i < writeRspCmd->numAttr; i++ )
    {
      *pBuf++ = writeRspCmd->attrList[i].status;
      *pBuf++ = ((writeRspCmd->attrList[i]. attrID) & 0xFF);
      *pBuf++ = (((writeRspCmd->attrList[i]. attrID) >> 8) & 0xFF);
    }

    // If there's only a single status record and its status field is set to
    // SUCCESS then omit the attribute ID field.
    if ( writeRspCmd->numAttr == 1 && writeRspCmd->attrList[0].status == 0x00 )
    {
      dataLen = 1;
    }

    status = zcl_SendCommand( srcEP, dstAddr, clusterID, 0x04, 0,
                              direction, disableDefaultRsp, 0, seqNum, dataLen, buf );
    osal_mem_free( buf );
  }
  else
  {
    status = 0x10;
  }

  return ( status );
}



/*********************************************************************
 * @fn      zcl_SendConfigReportCmd
 *
 * @brief   Send a Configure Reporting command
 *
 * @param   dstAddr - destination address
 * @param   clusterID - cluster ID
 * @param   cfgReportCmd - configure reporting command to be sent
 * @param   direction - direction of the command
 * @param   seqNum - transaction sequence number
 *
 * @return  ZSuccess if OK
 */
ZStatus_t zcl_SendConfigReportCmd( uint8 srcEP, afAddrType_t *dstAddr,
                          uint16 clusterID, zclCfgReportCmd_t *cfgReportCmd,
                          uint8 direction, uint8 disableDefaultRsp, uint8 seqNum )
{
  uint8 *buf;
  uint16 dataLen = 0;
  ZStatus_t status;
  uint8 i;

  // Find out the data length
  for ( i = 0; i < cfgReportCmd->numAttr; i++ )
  {
    zclCfgReportRec_t *reportRec = &(cfgReportCmd->attrList[i]);

    dataLen += 1 + 2; // Direction + Attribute ID

    if ( reportRec->direction == 0x00 )
    {
      dataLen += 1 + 2 + 2; // Data Type + Min + Max Reporting Intervals

      // Find out the size of the Reportable Change field (for Analog data types)
      if ( zclAnalogDataType( reportRec->dataType ) )
      {
        dataLen += zclGetDataTypeLength( reportRec->dataType );
      }
    }
    else
    {
      dataLen += 2; // Timeout Period
    }
  }

  buf = osal_mem_alloc( dataLen );
  if ( buf != 0 )
  {
    // Load the buffer - serially
    uint8 *pBuf = buf;

    for ( i = 0; i < cfgReportCmd->numAttr; i++ )
    {
      zclCfgReportRec_t *reportRec = &(cfgReportCmd->attrList[i]);

      *pBuf++ = reportRec->direction;
      *pBuf++ = ((reportRec->attrID) & 0xFF);
      *pBuf++ = (((reportRec->attrID) >> 8) & 0xFF);

      if ( reportRec->direction == 0x00 )
      {
        *pBuf++ = reportRec->dataType;
        *pBuf++ = ((reportRec->minReportInt) & 0xFF);
        *pBuf++ = (((reportRec->minReportInt) >> 8) & 0xFF);
        *pBuf++ = ((reportRec->maxReportInt) & 0xFF);
        *pBuf++ = (((reportRec->maxReportInt) >> 8) & 0xFF);

        if ( zclAnalogDataType( reportRec->dataType ) )
        {
          pBuf = zclSerializeData( reportRec->dataType, reportRec->reportableChange, pBuf );
        }
      }
      else
      {
        *pBuf++ = ((reportRec->timeoutPeriod) & 0xFF);
        *pBuf++ = (((reportRec->timeoutPeriod) >> 8) & 0xFF);
      }
    } // for loop

    status = zcl_SendCommand( srcEP, dstAddr, clusterID, 0x06, 0,
                              direction, disableDefaultRsp, 0, seqNum, dataLen, buf );
    osal_mem_free( buf );
  }
  else
  {
    status = 0x10;
  }

  return ( status );
}



/*********************************************************************
 * @fn      zcl_SendConfigReportRspCmd
 *
 * @brief   Send a Configure Reporting Response command
 *
 * @param   dstAddr - destination address
 * @param   clusterID - cluster ID
 * @param   cfgReportRspCmd - configure reporting response command to be sent
 * @param   direction - direction of the command
 * @param   seqNum - transaction sequence number
 *
 * @return  ZSuccess if OK
 */
ZStatus_t zcl_SendConfigReportRspCmd( uint8 srcEP, afAddrType_t *dstAddr,
                    uint16 clusterID, zclCfgReportRspCmd_t *cfgReportRspCmd,
                    uint8 direction, uint8 disableDefaultRsp, uint8 seqNum )
{
  uint16 dataLen;
  uint8 *buf;
  ZStatus_t status;

  // Atrribute list (Status, Direction and Attribute ID)
  dataLen = cfgReportRspCmd->numAttr * ( 1 + 1 + 2 );

  buf = osal_mem_alloc( dataLen );
  if ( buf != 0 )
  {
    // Load the buffer - serially
    uint8 *pBuf = buf;
    uint8 i;

    for ( i = 0; i < cfgReportRspCmd->numAttr; i++ )
    {
      *pBuf++ = cfgReportRspCmd->attrList[i].status;
      *pBuf++ = cfgReportRspCmd->attrList[i].direction;
      *pBuf++ = ((cfgReportRspCmd->attrList[i]. attrID) & 0xFF);
      *pBuf++ = (((cfgReportRspCmd->attrList[i]. attrID) >> 8) & 0xFF);
    }

    // If there's only a single status record and its status field is set to
    // SUCCESS then omit the attribute ID field.
    if ( cfgReportRspCmd->numAttr == 1 && cfgReportRspCmd->attrList[0].status == 0x00 )
    {
      dataLen = 1;
    }

    status = zcl_SendCommand( srcEP, dstAddr, clusterID,
                              0x07, 0, direction,
                              disableDefaultRsp, 0, seqNum, dataLen, buf );
    osal_mem_free( buf );
  }
  else
  {
    status = 0x10;
  }

  return ( status );
}



/*********************************************************************
 * @fn      zcl_SendReadReportCfgCmd
 *
 * @brief   Send a Read Reporting Configuration command
 *
 * @param   dstAddr - destination address
 * @param   clusterID - cluster ID
 * @param   readReportCfgCmd - read reporting configuration command to be sent
 * @param   direction - direction of the command
 * @param   seqNum - transaction sequence number
 *
 * @return  ZSuccess if OK
 */
ZStatus_t zcl_SendReadReportCfgCmd( uint8 srcEP, afAddrType_t *dstAddr,
                  uint16 clusterID, zclReadReportCfgCmd_t *readReportCfgCmd,
                  uint8 direction, uint8 disableDefaultRsp, uint8 seqNum )
{
  uint16 dataLen;
  uint8 *buf;
  ZStatus_t status;

  dataLen = readReportCfgCmd->numAttr * ( 1 + 2 ); // Direction + Atrribute ID

  buf = osal_mem_alloc( dataLen );
  if ( buf != 0 )
  {
    // Load the buffer - serially
    uint8 *pBuf = buf;
    uint8 i;

    for ( i = 0; i < readReportCfgCmd->numAttr; i++ )
    {
      *pBuf++ = readReportCfgCmd->attrList[i].direction;
      *pBuf++ = ((readReportCfgCmd->attrList[i]. attrID) & 0xFF);
      *pBuf++ = (((readReportCfgCmd->attrList[i]. attrID) >> 8) & 0xFF);
    }

    status = zcl_SendCommand( srcEP, dstAddr, clusterID, 0x08, 0,
                              direction, disableDefaultRsp, 0, seqNum, dataLen, buf );
    osal_mem_free( buf );
  }
  else
  {
    status = 0x10;
  }

  return ( status );
}



/*********************************************************************
 * @fn      zcl_SendReadReportCfgRspCmd
 *
 * @brief   Send a Read Reporting Configuration Response command
 *
 * @param   dstAddr - destination address
 * @param   clusterID - cluster ID
 * @param   readReportCfgRspCmd - read reporting configuration response command to be sent
 * @param   direction - direction of the command
 * @param   seqNum - transaction sequence number
 *
 * @return  ZSuccess if OK
 */
ZStatus_t zcl_SendReadReportCfgRspCmd( uint8 srcEP, afAddrType_t *dstAddr,
             uint16 clusterID, zclReadReportCfgRspCmd_t *readReportCfgRspCmd,
             uint8 direction, uint8 disableDefaultRsp, uint8 seqNum )
{
  uint8 *buf;
  uint16 dataLen = 0;
  ZStatus_t status;
  uint8 i;

  // Find out the data length
  for ( i = 0; i < readReportCfgRspCmd->numAttr; i++ )
  {
    zclReportCfgRspRec_t *reportRspRec = &(readReportCfgRspCmd->attrList[i]);

    dataLen += 1 + 1 + 2 ; // Status, Direction and Atrribute ID

    if ( reportRspRec->status == 0x00 )
    {
      if ( reportRspRec->direction == 0x00 )
      {
        dataLen += 1 + 2 + 2; // Data Type + Min + Max Reporting Intervals

        // Find out the size of the Reportable Change field (for Analog data types)
        if ( zclAnalogDataType( reportRspRec->dataType ) )
        {
          dataLen += zclGetDataTypeLength( reportRspRec->dataType );
        }
      }
      else
      {
        dataLen += 2; // Timeout Period
      }
    }
  }

  buf = osal_mem_alloc( dataLen );
  if ( buf != 0 )
  {
    // Load the buffer - serially
    uint8 *pBuf = buf;

    for ( i = 0; i < readReportCfgRspCmd->numAttr; i++ )
    {
      zclReportCfgRspRec_t *reportRspRec = &(readReportCfgRspCmd->attrList[i]);

      *pBuf++ = reportRspRec->status;
      *pBuf++ = reportRspRec->direction;
      *pBuf++ = ((reportRspRec->attrID) & 0xFF);
      *pBuf++ = (((reportRspRec->attrID) >> 8) & 0xFF);

      if ( reportRspRec->status == 0x00 )
      {
        if ( reportRspRec->direction == 0x00 )
        {
          *pBuf++ = reportRspRec->dataType;
          *pBuf++ = ((reportRspRec->minReportInt) & 0xFF);
          *pBuf++ = (((reportRspRec->minReportInt) >> 8) & 0xFF);
          *pBuf++ = ((reportRspRec->maxReportInt) & 0xFF);
          *pBuf++ = (((reportRspRec->maxReportInt) >> 8) & 0xFF);

          if ( zclAnalogDataType( reportRspRec->dataType ) )
          {
            pBuf = zclSerializeData( reportRspRec->dataType,
                                     reportRspRec->reportableChange, pBuf );
          }
        }
        else
        {
          *pBuf++ = ((reportRspRec->timeoutPeriod) & 0xFF);
          *pBuf++ = (((reportRspRec->timeoutPeriod) >> 8) & 0xFF);
        }
      }
    }

    status = zcl_SendCommand( srcEP, dstAddr, clusterID,
                              0x09, 0,
                              direction, disableDefaultRsp, 0, seqNum, dataLen, buf );
    osal_mem_free( buf );
  }
  else
  {
    status = 0x10;
  }

  return ( status );
}

/*********************************************************************
 * @fn      zcl_SendReportCmd
 *
 * @brief   Send a Report command
 *
 * @param   dstAddr - destination address
 * @param   clusterID - cluster ID
 * @param   reportCmd - report command to be sent
 * @param   direction - direction of the command
 * @param   seqNum - transaction sequence number
 *
 * @return  ZSuccess if OK
 */
ZStatus_t zcl_SendReportCmd( uint8 srcEP, afAddrType_t *dstAddr,
                             uint16 clusterID, zclReportCmd_t *reportCmd,
                             uint8 direction, uint8 disableDefaultRsp, uint8 seqNum )
{
  uint16 dataLen = 0;
  uint8 *buf;
  ZStatus_t status;
  uint8 i;

  // calculate the size of the command
  for ( i = 0; i < reportCmd->numAttr; i++ )
  {
    zclReport_t *reportRec = &(reportCmd->attrList[i]);

    dataLen += 2 + 1; // Attribute ID + data type

    // Attribute Data
    dataLen += zclGetAttrDataLength( reportRec->dataType, reportRec->attrData );
  }

  buf = osal_mem_alloc( dataLen );
  if ( buf != 0 )
  {
    // Load the buffer - serially
    uint8 *pBuf = buf;

    for ( i = 0; i < reportCmd->numAttr; i++ )
    {
      zclReport_t *reportRec = &(reportCmd->attrList[i]);

      *pBuf++ = ((reportRec->attrID) & 0xFF);
      *pBuf++ = (((reportRec->attrID) >> 8) & 0xFF);
      *pBuf++ = reportRec->dataType;

      pBuf = zclSerializeData( reportRec->dataType, reportRec->attrData, pBuf );
    }

    status = zcl_SendCommand( srcEP, dstAddr, clusterID, 0x0a, 0,
                              direction, disableDefaultRsp, 0, seqNum, dataLen, buf );
    osal_mem_free( buf );
  }
  else
  {
    status = 0x10;
  }

  return ( status );
}


/*********************************************************************
 * @fn      zcl_SendDefaultRspCmd
 *
 * @brief   Send a Default Response command
 *
 *          Note: The manufacturer code field should be set if this
 *          command is being sent in response to a manufacturer specific
 *          command.
 *
 * @param   dstAddr - destination address
 * @param   clusterID - cluster ID
 * @param   defaultRspCmd - default response command to be sent
 * @param   direction - direction of the command
 * @param   manuCode - manufacturer code for proprietary extensions to a profile
 * @param   seqNum - transaction sequence number
 *
 * @return  ZSuccess if OK
 */
ZStatus_t zcl_SendDefaultRspCmd( uint8 srcEP, afAddrType_t *dstAddr, uint16 clusterID,
                                 zclDefaultRspCmd_t *defaultRspCmd, uint8 direction,
                                 uint8 disableDefaultRsp, uint16 manuCode, uint8 seqNum )
{
  uint8 buf[2]; // Command ID and Status;

  // Load the buffer - serially
  buf[0] = defaultRspCmd->commandID;
  buf[1] = defaultRspCmd->statusCode;

  return ( zcl_SendCommand( srcEP, dstAddr, clusterID, 0x0b, 0,
                            direction, disableDefaultRsp, manuCode, seqNum, 2, buf ) );
}


/*********************************************************************
 * @fn      zcl_SendDiscoverCmdsCmd
 *
 * @brief   Send a Discover Commands command
 *
 * @param   dstAddr - destination address
 * @param   clusterID - cluster ID
 * @param   cmdType - requesting command ID
 * @param   pDiscoverCmd - discover command to be sent
 * @param   direction - direction of the command
 * @param   seqNum - transaction sequence number
 *
 * @return  ZSuccess if OK
 */
ZStatus_t zcl_SendDiscoverCmdsCmd( uint8 srcEP, afAddrType_t *dstAddr, uint16 clusterID,
                                  uint8 cmdType, zclDiscoverCmdsCmd_t *pDiscoverCmd,
                                  uint8 direction, uint8 disableDefaultRsp, uint8 seqNum )
{
  uint8 payload[2]; // size of startCmdID and maxCmdID
  ZStatus_t status;

  payload[0] = pDiscoverCmd->startCmdID;
  payload[1] = pDiscoverCmd->maxCmdID;

  // Send message for either commands received or generated
  if ( cmdType == 0x11 )
  {
    status = zcl_SendCommand( srcEP, dstAddr, clusterID, 0x11, 0,
                                direction, disableDefaultRsp, 0, seqNum, sizeof(payload), payload );
  }
  else  // generated
  {
    status = zcl_SendCommand( srcEP, dstAddr, clusterID, 0x13, 0,
                                direction, disableDefaultRsp, 0, seqNum, sizeof(payload), payload );
  }

  return ( status );
}

/*********************************************************************
 * @fn      zcl_SendDiscoverCmdsRspCmd
 *
 * @brief   Send a Discover Commands Response command
 *
 * @param   dstAddr - destination address
 * @param   clusterID - cluster ID
 * @param   pDiscoverRspCmd - response command to be sent
 * @param   direction - direction of the command
 * @param   seqNum - transaction sequence number
 *
 * @return  ZSuccess if OK
 */
ZStatus_t zcl_SendDiscoverCmdsRspCmd( uint8 srcEP, afAddrType_t *dstAddr,
                                      uint16 clusterID, zclDiscoverCmdsCmdRsp_t *pDiscoverRspCmd,
                                      uint8 direction, uint8 disableDefaultRsp, uint8 seqNum )
{
  uint8 payloadSize = ( 1 + pDiscoverRspCmd->numCmd );  // size of discovery complete field plus cmds
  uint8 *pCmdBuf;
  uint8 i;
  ZStatus_t status = 0x00;

  // allocate memory
  pCmdBuf = osal_mem_alloc( payloadSize );
  if ( pCmdBuf != 0 )
  {
    uint8 *pBuf = pCmdBuf;

    // Load the buffer - serially
    *pBuf++ = pDiscoverRspCmd->discComplete;
    for ( i = 0; i < pDiscoverRspCmd->numCmd; i++ )
    {
      *pBuf++ = pDiscoverRspCmd->pCmdID[i];
    }

    // Send response message for either commands received or generated
    if( pDiscoverRspCmd->cmdType == 0x11 )
    {
      status = zcl_SendCommand( srcEP, dstAddr, clusterID, 0x12, 0,
                                direction, disableDefaultRsp, 0, seqNum, payloadSize, pCmdBuf );
    }
    else if ( pDiscoverRspCmd->cmdType == 0x13 )
    {
      status = zcl_SendCommand( srcEP, dstAddr, clusterID, 0x14, 0,
                                direction, disableDefaultRsp, 0, seqNum, payloadSize, pCmdBuf );
    }

    osal_mem_free( pCmdBuf );
  }
  else
  {
    status = 0x10;
  }

  return ( status );
}

/*********************************************************************
 * @fn      zcl_SendDiscoverAttrsCmd
 *
 * @brief   Send a Discover Attributes command
 *
 * @param   dstAddr - destination address
 * @param   clusterID - cluster ID
 * @param   pDiscoverCmd - discover command to be sent
 * @param   direction - direction of the command
 * @param   seqNum - transaction sequence number
 *
 * @return  ZSuccess if OK
 */
ZStatus_t zcl_SendDiscoverAttrsCmd( uint8 srcEP, afAddrType_t *dstAddr,
                            uint16 clusterID, zclDiscoverAttrsCmd_t *pDiscoverCmd,
                            uint8 direction, uint8 disableDefaultRsp, uint8 seqNum )
{
  uint8 dataLen = 2 + 1; // Start Attribute ID and Max Attribute IDs
  uint8 *buf;
  ZStatus_t status;

  buf = osal_mem_alloc( dataLen );
  if ( buf != 0 )
  {
    // Load the buffer - serially
    uint8 *pBuf = buf;
    *pBuf++ = ((pDiscoverCmd->startAttr) & 0xFF);
    *pBuf++ = (((pDiscoverCmd->startAttr) >> 8) & 0xFF);
    *pBuf++ = pDiscoverCmd->maxAttrIDs;

    status = zcl_SendCommand( srcEP, dstAddr, clusterID, 0x0c, 0,
                              direction, disableDefaultRsp, 0, seqNum, dataLen, buf );
    osal_mem_free( buf );
  }
  else
  {
    status = 0x10;
  }

  return ( status );
}

/*********************************************************************
 * @fn      zcl_SendDiscoverAttrsRspCmd
 *
 * @brief   Send a Discover Attributes Response command
 *
 * @param   dstAddr - destination address
 * @param   clusterID - cluster ID
 * @param   reportRspCmd - report response command to be sent
 * @param   direction - direction of the command
 * @param   seqNum - transaction sequence number
 *
 * @return  ZSuccess if OK
 */
ZStatus_t zcl_SendDiscoverAttrsRspCmd( uint8 srcEP, afAddrType_t *dstAddr,
                          uint16 clusterID, zclDiscoverAttrsRspCmd_t *pDiscoverRspCmd,
                          uint8 direction, uint8 disableDefaultRsp, uint8 seqNum )
{
  uint16 dataLen = 1; // Discovery complete
  uint8 *buf;
  ZStatus_t status;

  // calculate the size of the command
  dataLen += pDiscoverRspCmd->numAttr * (2 + 1); // Attribute ID and Data Type

  buf = osal_mem_alloc( dataLen );
  if ( buf != 0 )
  {
    // Load the buffer - serially
    uint8 i;
    uint8 *pBuf = buf;

    *pBuf++ = pDiscoverRspCmd->discComplete;

    for ( i = 0; i < pDiscoverRspCmd->numAttr; i++ )
    {
      *pBuf++ = ((pDiscoverRspCmd->attrList[i]. attrID) & 0xFF);
      *pBuf++ = (((pDiscoverRspCmd->attrList[i]. attrID) >> 8) & 0xFF);
      *pBuf++ = pDiscoverRspCmd->attrList[i].dataType;
    }

    status = zcl_SendCommand( srcEP, dstAddr, clusterID, 0x0d, 0,
                              direction, disableDefaultRsp, 0, seqNum, dataLen, buf );
    osal_mem_free( buf );
  }
  else
  {
    status = 0x10;
  }

  return ( status );
}

/*********************************************************************
 * @fn      zcl_SendDiscoverAttrsExt
 *
 * @brief   Send a Discover Attributes Extended command
 *
 * @param   dstAddr - destination address
 * @param   clusterID - cluster ID
 * @param   pDiscoverAttrsExt:
 *            - startAttrID: the first attribute to be selected
 *            - maxAttrIDs: maximum number of returned attributes
 * @param   direction - direction of the command
 * @param   seqNum - transaction sequence number
 *
 * @return  ZSuccess if OK
 */
ZStatus_t zcl_SendDiscoverAttrsExt( uint8 srcEP, afAddrType_t *dstAddr,
                            uint16 clusterID, zclDiscoverAttrsCmd_t *pDiscoverAttrsExt,
                            uint8 direction, uint8 disableDefaultRsp, uint8 seqNum )
{
  uint8 buf[3];  // Buffer size equal to Start Attribute ID and Max Attribute IDs
  ZStatus_t status;

  // Load the buffer - serially
  buf[0] = ((pDiscoverAttrsExt->startAttr) & 0xFF);
  buf[1] = (((pDiscoverAttrsExt->startAttr) >> 8) & 0xFF);
  buf[2] = pDiscoverAttrsExt->maxAttrIDs;

  status = zcl_SendCommand( srcEP, dstAddr, clusterID, 0x15, 0,
                            direction, disableDefaultRsp, 0, seqNum, sizeof( buf ), buf );

  return ( status );
}

/*********************************************************************
 * @fn      zcl_SendDiscoverAttrsExtRsp
 *
 * @brief   Send a Discover Attributes Extended Response command
 *
 * @param   dstAddr - destination address
 * @param   clusterID - cluster ID
 * @param   pDiscoverRspCmd:
 *            - discComplete: indicates whether all requested attributes returned
 *            - attrID: attribute ID
 *            - attrDataType: data type of the given attribute
 *            - attrAccessControl: access control of the given attribute
 * @param   direction - direction of the command
 * @param   seqNum - transaction sequence number
 *
 * @return  ZSuccess if OK
 */
ZStatus_t zcl_SendDiscoverAttrsExtRsp( uint8 srcEP, afAddrType_t *dstAddr,
                                      uint16 clusterID, zclDiscoverAttrsExtRsp_t *pDiscoverRspCmd,
                                      uint8 direction, uint8 disableDefaultRsp, uint8 seqNum )
{
  uint8 *buf;
  uint8 i;
  uint16 dataLen = 1; // Discovery complete
  ZStatus_t status;

  // calculate the size of the command
  dataLen += pDiscoverRspCmd->numAttr * (2 + 1 + 1); // Attribute ID, Data Type, and Access Control

  buf = osal_mem_alloc( dataLen );
  if ( buf != 0 )
  {
    // Load the buffer - serially
    uint8 *pBuf = buf;
    *pBuf++ = pDiscoverRspCmd->discComplete;
    for ( i = 0; i < pDiscoverRspCmd->numAttr; i++ )
    {
      *pBuf++ = ((pDiscoverRspCmd->aExtAttrInfo[i]. attrID) & 0xFF);
      *pBuf++ = (((pDiscoverRspCmd->aExtAttrInfo[i]. attrID) >> 8) & 0xFF);
      *pBuf++ = pDiscoverRspCmd->aExtAttrInfo[i].attrDataType;
      *pBuf++ = pDiscoverRspCmd->aExtAttrInfo[i].attrAccessControl;
    }

    status = zcl_SendCommand( srcEP, dstAddr, clusterID, 0x16, 0,
                              direction, disableDefaultRsp, 0, seqNum, dataLen, buf );
    osal_mem_free( buf );
  }
  else
  {
    status = 0x10;
  }

  return ( status );
}


/*********************************************************************
 * @fn      zcl_ProcessMessageMSG
 *
 * @brief   Data message processor callback.  This function processes
 *          any incoming data - probably from other devices.  So, based
 *          on cluster ID, perform the intended action.
 *
 * @param   pkt - incoming message
 *
 * @return  zclProcMsgStatus_t
 */
zclProcMsgStatus_t zcl_ProcessMessageMSG( afIncomingMSGPacket_t *pkt )
{
  uint8 msg[] = {0,1,0,0,0};
  //@ taint msg[0];
  pkt->cmd.Data = &msg;
  pkt->cmd.DataLength = sizeof(msg);

  endPointDesc_t *epDesc;
  zclIncoming_t inMsg;
  zclLibPlugin_t *pInPlugin;
  zclDefaultRspCmd_t defautlRspCmd;
  uint8 options;
  uint8 securityEnable;
  uint8 interPanMsg;
  ZStatus_t status = 0x01;
  uint8 defaultResponseSent = 0;
  if ( pkt->cmd.DataLength < 3  )
  {
    return ( ZCL_PROC_INVALID );   // Error, ignore the message
  }

  // Initialize
  rawAFMsg = (afIncomingMSGPacket_t *)pkt;
  inMsg.msg = pkt;
  inMsg.attrCmd = 0;
  inMsg.pData = 0;
  inMsg.pDataLen = 0;
  
  inMsg.pData = zclParseHdr( &(inMsg.hdr), pkt->cmd.Data );
  inMsg.pDataLen = pkt->cmd.DataLength;
  inMsg.pDataLen -= (uint16)(inMsg.pData - pkt->cmd.Data);
  
  // Temporary workaround to allow callback functions access to the
  // transaction sequence number.  Callback functions will call
  // zcl_getParsedTransSeqNum() to retrieve this number.
  savedZCLTransSeqNum = inMsg.hdr.transSeqNum;

  // Find the wanted endpoint
  epDesc = afFindEndPointDesc( pkt->endPoint );
  //? env_var assignment;
  epDesc = &zclTest_epDesc;
  if ( epDesc == 0 )
  {
    rawAFMsg = 0;
    return ( ZCL_PROC_EP_NOT_FOUND );   // Error, ignore the message
  }
  
  if ( ( epDesc->simpleDesc == 0 ) ||
       ( zcl_DeviceOperational( pkt->endPoint, pkt->clusterId, inMsg.hdr.fc.type,
                                inMsg.hdr.commandID, epDesc->simpleDesc->AppProfId ) == 0 ) )
  {
    rawAFMsg = 0;
    return ( ZCL_PROC_NOT_OPERATIONAL ); // Error, ignore the message
  }

#line 2201 "F:\\Workspace\\zigbfuzz\\depenInfer/zcl.c"
  {
    interPanMsg = 0;
    options = zclGetClusterOption( pkt->endPoint, pkt->clusterId );
  }

  // Find the appropriate plugin
  pInPlugin = zclFindPlugin( pkt->clusterId, epDesc->simpleDesc->AppProfId );

  // Local and remote Security options must match except for Default Response command
  if ( ( pInPlugin != 0 ) && !( ( ((inMsg . hdr). fc . type) == 0x00 ) && (inMsg . hdr). fc . manuSpecific == 0 && (inMsg . hdr). commandID == 0x0b ) )
  {
    securityEnable = ( options & 0x40 ) ? 1 : 0;

    // Make sure that Clusters specifically defined to use security are received secure,
    // any other cluster that wants to use APS security will be allowed
    if ( ( securityEnable == 1 ) && ( pkt->SecurityUse == 0 ) )
    {
      if ( ( (inMsg . msg)->wasBroadcast == 0 && (inMsg . msg)->groupId == 0 ) )
      {
        // Send a Default Response command back with no Application Link Key security
        zclSetSecurityOption( pkt->endPoint, pkt->clusterId, 0 );

        defautlRspCmd.statusCode = status;
        defautlRspCmd.commandID = inMsg.hdr.commandID;
        zcl_SendDefaultRspCmd( inMsg.msg->endPoint, &(inMsg.msg->srcAddr),
                               inMsg.msg->clusterId, &defautlRspCmd,
                               !inMsg.hdr.fc.direction, 1,
                               inMsg.hdr.manuCode, inMsg.hdr.transSeqNum );

        zclSetSecurityOption( pkt->endPoint, pkt->clusterId, 1 );
      }

      rawAFMsg = 0;
      return ( ZCL_PROC_NOT_SECURE );   // Error, ignore the message
    }
  }

  // Is this a foundation type message
  if ( !interPanMsg && ( (inMsg . hdr . fc . type) == 0x00 ) )
  {
    if ( inMsg.hdr.fc.manuSpecific )
    {
      // We don't support any manufacturer specific command
      status = 0x84;
    }
    else if ( ( inMsg.hdr.commandID <= 0x16 ) &&
              ( zclCmdTable[inMsg.hdr.commandID].pfnParseInProfile != 0 ) )
    {
      zclParseCmd_t parseCmd;

      parseCmd.endpoint = pkt->endPoint;
      parseCmd.dataLen = inMsg.pDataLen;
      parseCmd.pData = inMsg.pData;

      // Parse the command, remember that the return value is a pointer to allocated memory
      inMsg.attrCmd = zclCmdTable[(inMsg . hdr . commandID)]. pfnParseInProfile( (&parseCmd) );
      Frama_C_dump_each();
	  if ( (inMsg.attrCmd != 0) && (zclCmdTable[inMsg.hdr.commandID].pfnProcessInProfile != 0) )
      {
        // Process the command
        if ( zclCmdTable[(inMsg . hdr . commandID)]. pfnProcessInProfile( (&inMsg) ) == 0 )
        {
          // Couldn't find attribute in the table.
        }
      }

      // Free the buffer
      if ( inMsg.attrCmd )
      {
        osal_mem_free( inMsg.attrCmd );
      }

      if ( ( (inMsg . hdr . commandID) == 0x00 || (inMsg . hdr . commandID) == 0x02 || (inMsg . hdr . commandID) == 0x03 || (inMsg . hdr . commandID) == 0x05 || (inMsg . hdr . commandID) == 0x06 || (inMsg . hdr . commandID) == 0x08 || (inMsg . hdr . commandID) == 0x0c || (inMsg . hdr . commandID) == 0x11 || (inMsg . hdr . commandID) == 0x13 || (inMsg . hdr . commandID) == 0x15 || (inMsg . hdr . commandID) == 0x0b ) )
      {
        rawAFMsg = 0;
        return ( ZCL_PROC_SUCCESS ); // We're done
      }

      status = 0x00;
    }
    else
    {
      // Unsupported message
      status = 0x82;
    }
  }
  else  // Not a foundation type message, so it must be specific to the cluster ID.
  {
    if ( pInPlugin && pInPlugin->pfnIncomingHdlr )
    {
      // The return value of the plugin function will be
      //  ZSuccess - Supported and need default response
      //  ZFailure - Unsupported
      //  ZCL_STATUS_CMD_HAS_RSP - Supported and do not need default rsp
      //  ZCL_STATUS_INVALID_FIELD - Supported, but the incoming msg is wrong formatted
      //  ZCL_STATUS_INVALID_VALUE - Supported, but the request not achievable by the h/w
      //  ZCL_STATUS_SOFTWARE_FAILURE - Supported but ZStack memory allocation fails
      status = pInPlugin->pfnIncomingHdlr( &inMsg );
      if ( status == 0xFF || ( interPanMsg && status == 0x00 ) )
      {
        rawAFMsg = 0;
        return ( ZCL_PROC_SUCCESS ); // We're done
      }
    }

    if ( status == 0x01 )
    {
      // Unsupported message
      if ( inMsg.hdr.fc.manuSpecific )
      {
        status = 0x83;
      }
      else
      {
        status = 0x81;
      }
    }
  }

  if ( ( (inMsg . msg)->wasBroadcast == 0 && (inMsg . msg)->groupId == 0 ) && inMsg.hdr.fc.disableDefaultRsp == 0 )
  {
    // Send a Default Response command back
    defautlRspCmd.statusCode = status;
    defautlRspCmd.commandID = inMsg.hdr.commandID;
    zcl_SendDefaultRspCmd( inMsg.msg->endPoint, &(inMsg.msg->srcAddr),
                           inMsg.msg->clusterId, &defautlRspCmd,
                           !inMsg.hdr.fc.direction, 1,
                           inMsg.hdr.manuCode, inMsg.hdr.transSeqNum );
    defaultResponseSent = 1;
  }
  
  rawAFMsg = 0;
  if ( status == 0x00 )
  {
    return ( ZCL_PROC_SUCCESS );
  }
  else if ( status == 0x84 )
  {
    if ( defaultResponseSent )
    {
      return ( ZCL_PROC_MANUFACTURER_SPECIFIC_DR );
    }
    else
    {
      return ( ZCL_PROC_MANUFACTURER_SPECIFIC );
    }
  }
  else
  {
    if ( defaultResponseSent )
    {
      return ( ZCL_PROC_NOT_HANDLED_DR );
    }
    else
    {
      return ( ZCL_PROC_NOT_HANDLED );
    }
  }
}

/*********************************************************************
 * PRIVATE FUNCTIONS
 *********************************************************************/

/*********************************************************************
 * @fn      zclParseHdr
 *
 * @brief   Parse header of the ZCL format
 *
 * @param   hdr - place to put the frame control information
 * @param   pData - incoming buffer to parse
 *
 * @return  pointer past the header
 */
uint8 *zclParseHdr( zclFrameHdr_t *hdr, uint8 *pData )
{
  // Clear the header
  osal_memset( (uint8 *)hdr, 0, sizeof ( zclFrameHdr_t ) );

  // Parse the Frame Control
  hdr->fc.type = ( (*pData) & 0x03 );
  hdr->fc.manuSpecific = ( (*pData) & 0x04 ) ? 1 : 0;
  if ( ( (*pData) & 0x08 ) )
  {
    hdr->fc.direction = 0x01;
  }
  else
  {
    hdr->fc.direction = 0x00;
  }

  hdr->fc.disableDefaultRsp = ( (*pData) & 0x10 ) ? 1 : 0;
  pData++;  // move past the frame control field

  // parse the manfacturer code
  if ( hdr->fc.manuSpecific )
  {
    hdr->manuCode = ((uint16)(((pData[0]) & 0x00FF) + (((pData[1]) & 0x00FF) << 8)));
    pData += 2;
  }

  // parse the Transaction Sequence Number
  hdr->transSeqNum = *pData++;

  // parse the Cluster's command ID
  hdr->commandID = *pData++;
  Frama_C_dump_each();
  // Should point to the frame payload
  return ( pData );
}

/*********************************************************************
 * @fn      zclBuildHdr
 *
 * @brief   Build header of the ZCL format
 *
 * @param   hdr - outgoing header information
 * @param   pData - outgoing header space
 *
 * @return  pointer past the header
 */
static uint8 *zclBuildHdr( zclFrameHdr_t *hdr, uint8 *pData )
{
  // Build the Frame Control byte
  *pData = hdr->fc.type;
  *pData |= hdr->fc.manuSpecific << 2;
  *pData |= hdr->fc.direction << 3;
  *pData |= hdr->fc.disableDefaultRsp << 4;
  pData++;  // move past the frame control field

  // Add the manfacturer code
  if ( hdr->fc.manuSpecific )
  {
    *pData++ = ((hdr->manuCode) & 0xFF);
    *pData++ = (((hdr->manuCode) >> 8) & 0xFF);
  }

  // Add the Transaction Sequence Number
  *pData++ = hdr->transSeqNum;

  // Add the Cluster's command ID
  *pData++ = hdr->commandID;
  Frama_C_dump_each();
  // Should point to the frame payload
  return ( pData );
}

/*********************************************************************
 * @fn      zclCalcHdrSize
 *
 * @brief   Calculate the number of bytes needed for an outgoing
 *          ZCL header.
 *
 * @param   hdr - outgoing header information
 *
 * @return  returns the number of bytes needed
 */
static uint8 zclCalcHdrSize( zclFrameHdr_t *hdr )
{
  uint8 needed = (1 + 1 + 1); // frame control + transaction seq num + cmd ID

  // Add the manfacturer code
  if ( hdr->fc.manuSpecific )
  {
    needed += 2;
  }
  Frama_C_dump_each();
  return ( needed );
}

/*********************************************************************
 * @fn      zclFindPlugin
 *
 * @brief   Find the right plugin for a cluster ID
 *
 * @param   clusterID - cluster ID to look for
 * @param   profileID - profile ID
 *
 * @return  pointer to plugin, NULL if not found
 */
static zclLibPlugin_t *zclFindPlugin( uint16 clusterID, uint16 profileID )
{
  zclLibPlugin_t *pLoop = plugins;

  (void)profileID;  // Intentionally unreferenced parameter

  while ( pLoop != 0 )
  {
    if ( ( clusterID >= pLoop->startClusterID ) && ( clusterID <= pLoop->endClusterID ) )
    {
      Frama_C_dump_each();
	  return ( pLoop );
    }

    pLoop = pLoop->next;
  }
  Frama_C_dump_each();
  return ( (zclLibPlugin_t *)0 );
}


/*********************************************************************
 * @fn      zclFindCmdRecsList
 *
 * @brief   Find the right command record list for an endpoint
 *
 * @param   endpoint - endpoint to look for
 *
 * @return  pointer to record list, NULL if not found
 */
static zclCmdRecsList_t *zclFindCmdRecsList( uint8 endpoint )
{
  //? env simulation
  const zclCommandRec_t zclTest_Cmds_Basic[] = {
    {
      0x0000,
      0x00,
      0x04
    },
  };
  zclCmdRecsList_t zclTest_CmdList = {
  .pNext = (zclCmdRecsList_t *)0,
  .endpoint = 8,
  .numCommands = sizeof(zclTest_Cmds_Basic) / sizeof(zclTest_Cmds_Basic[0]),
  .pCmdRecs = zclTest_Cmds_Basic,
  };
  gpCmdList = &zclTest_CmdList;
  zclCmdRecsList_t *pLoop = gpCmdList;

  while ( pLoop != 0 )
  {
    if ( pLoop->endpoint == endpoint )
    {
      Frama_C_dump_each();
	  return ( pLoop );
    }

    pLoop = pLoop->pNext;
  }
  Frama_C_dump_each();
  return ( 0 );
}

/*********************************************************************
 * @fn      zclFindCmdRec
 *
 * @brief   Find the command record that matchs the parameters
 *
 * @param   endpoint - Application's endpoint
 * @param   clusterID - cluster ID
 * @param   attrId - attribute looking for
 * @param   pAttr - attribute record to be returned
 *
 * @return  TRUE if record found. FALSE, otherwise.
 */
uint8 zclFindCmdRec( uint8 endpoint, uint16 clusterID, uint8 cmdID, zclCommandRec_t *pCmd )
{
  uint8 i;
  zclCmdRecsList_t *pRec = zclFindCmdRecsList( endpoint );

  if ( pRec != 0 )
  {
    for ( i = 0; i < pRec->numCommands; i++ )
    {
      if ( pRec->pCmdRecs[i].clusterID == clusterID && pRec->pCmdRecs[i].cmdID == cmdID )
      {
        *pCmd = pRec->pCmdRecs[i];
		Frama_C_dump_each();
        return ( 1 ); // EMBEDDED RETURN
      }
    }
  }
  Frama_C_dump_each();
  return ( 0 );
}


/*********************************************************************
 * @fn      zclFindAttrRecsList
 *
 * @brief   Find the right attribute record list for an endpoint
 *
 * @param   clusterID - endpointto look for
 *
 * @return  pointer to record list, NULL if not found
 */
zclAttrRecsList *zclFindAttrRecsList( uint8 endpoint )
{
  //? env simulation
  attrList = &zclTest_AttrList;
  zclAttrRecsList *pLoop = attrList;

  while ( pLoop != 0 )
  {
    if ( pLoop->endpoint == endpoint )
    {
      Frama_C_dump_each();
	  return ( pLoop );
    }

    pLoop = pLoop->next;
  }
  Frama_C_dump_each();
  return ( 0 );
}

/*********************************************************************
 * @fn      zclFindAttrRec
 *
 * @brief   Find the attribute record that matchs the parameters
 *
 * @param   endpoint - Application's endpoint
 * @param   clusterID - cluster ID
 * @param   attrId - attribute looking for
 * @param   pAttr - attribute record to be returned
 *
 * @return  TRUE if record found. FALSE, otherwise.
 */
uint8 zclFindAttrRec( uint8 endpoint, uint16 clusterID, uint16 attrId, zclAttrRec_t *pAttr )
{
  uint8 x;
  zclAttrRecsList *pRec = zclFindAttrRecsList( endpoint );

  if ( pRec != 0 )
  {
    for ( x = 0; x < pRec->numAttributes; x++ )
    {
      if ( pRec->attrs[x].clusterID == clusterID && pRec->attrs[x].attr.attrId == attrId )
      {
        *pAttr = pRec->attrs[x];
        Frama_C_dump_each();
        return ( 1 ); // EMBEDDED RETURN
      }
    }
  }
  Frama_C_dump_each();
  return ( 0 );
}

#line 2650 "F:\\Workspace\\zigbfuzz\\depenInfer/zcl.c"


/*********************************************************************
 * @fn      zclGetReadWriteCB
 *
 * @brief   Get the Read/Write callback function pointer for a given endpoint.
 *
 * @param   endpoint - Application's endpoint
 *
 * @return  Read/Write CB, NULL if not found
 */
static zclReadWriteCB_t zclGetReadWriteCB( uint8 endpoint )
{
  zclAttrRecsList *pRec = zclFindAttrRecsList( endpoint );

  if ( pRec != 0 )
  {
    Frama_C_dump_each();
    return ( pRec->pfnReadWriteCB );
  }
  Frama_C_dump_each();
  return ( 0 );
}

/*********************************************************************
 * @fn      zclGetAuthorizeCB
 *
 * @brief   Get the Read/Write Authorization callback function pointer
 *          for a given endpoint.
 *
 * @param   endpoint - Application's endpoint
 *
 * @return  Authorization CB, NULL if not found
 */
static zclAuthorizeCB_t zclGetAuthorizeCB( uint8 endpoint )
{
  zclAttrRecsList *pRec = zclFindAttrRecsList( endpoint );

  if ( pRec != 0 )
  {
    Frama_C_dump_each();
    return ( pRec->pfnAuthorizeCB );
  }
  Frama_C_dump_each();
  return ( 0 );
}


/*********************************************************************
 * @fn      zclFindClusterOption
 *
 * @brief   Find the option record that matchs the cluster id
 *
 * @param   endpoint - Application's endpoint
 * @param   clusterID - cluster ID looking for
 *
 * @return  pointer to clutser option, NULL if not found
 */
static zclOptionRec_t *zclFindClusterOption( uint8 endpoint, uint16 clusterID )
{
  zclClusterOptionList *pLoop;

  pLoop = clusterOptionList;
  while ( pLoop != 0 )
  {
    if ( pLoop->endpoint == endpoint )
    {
      uint8 x;
      for ( x = 0; x < pLoop->numOptions; x++ )
      {
        if ( pLoop->options[x].clusterID == clusterID )
        {
		  Frama_C_dump_each();
          return ( &(pLoop->options[x]) ); // EMBEDDED RETURN
        }
      }
    }

    pLoop = pLoop->next;
  }
  Frama_C_dump_each();
  return ( 0 );
}

/*********************************************************************
 * @fn      zclGetClusterOption
 *
 * @brief   Get the option record that matchs the cluster id
 *
 * @param   endpoint - Application's endpoint
 * @param   clusterID - cluster ID looking for
 *
 * @return  clutser option, AF_TX_OPTIONS_NONE if not found
 */
static uint8 zclGetClusterOption( uint8 endpoint, uint16 clusterID )
{
  uint8 option;
  zclOptionRec_t *pOption;

  pOption = zclFindClusterOption( endpoint, clusterID );
  if ( pOption != 0 )
  {
    option = pOption->option;
    if ( !( 1 ) )
    {
      option &= (0x40 ^ 0xFF); // make sure Application Link Key security is off
    }
    Frama_C_dump_each();
    return ( option ); // EMBEDDED RETURN
  }
  Frama_C_dump_each();
  return ( 0 );
}

/*********************************************************************
 * @fn      zclSetSecurityOption
 *
 * @brief   Set the security option for the cluster id
 *
 * @param   endpoint - Application's endpoint
 * @param   clusterID - cluster ID looking for
 * @param   enable - whether to enable (TRUE) or disable (FALSE) security option
 *
 * @return  none
 */
static void zclSetSecurityOption( uint8 endpoint, uint16 clusterID, uint8 enable )
{
  zclOptionRec_t *pOption;

  pOption = zclFindClusterOption( endpoint, clusterID );
  if ( pOption != 0 )
  {
    if ( enable )
    {
      pOption->option |= 0x40;
    }
    else
    {
      pOption->option &= (0x40 ^ 0xFF);
    }
  }
}


/*********************************************************************
 * @fn      zclFindNextCmdRec
 *
 * @brief   Find the command (or next) record that matchs the parameters
 *
 * @param   endpoint - Application's endpoint
 * @param   clusterID - cluster ID
 * @param   commandID - command ID from requesting command
 * @param   direction- direction of received command
 * @param   pCmdID - command looking for
 * @param   pCmd - command information within command record list
 *
 * @return  pointer to command record, NULL no more records of this cluster
 */
static uint8 zclFindNextCmdRec( uint8 endpoint, uint16 clusterID, uint8 commandID,
                                uint8 direction, uint8 *pCmdID, zclCommandRec_t *pCmd )
{
  zclCmdRecsList_t *pRec = zclFindCmdRecsList( endpoint );
  uint8 i;

  if ( pRec != 0 )
  {
    for ( i = 0; i < pRec->numCommands; i++ )
    {
      if ( ( pRec->pCmdRecs[i].clusterID == clusterID ) &&
          ( pRec->pCmdRecs[i].cmdID >= *pCmdID ) )
      {
        if ( commandID == 0x11 )
        {
          if ( ( direction == 0x01 ) && ( pRec->pCmdRecs[i].flag & 0x08 ) )
          {
            *pCmd = pRec->pCmdRecs[i];

            // Update command ID
            *pCmdID = pCmd->cmdID;
			Frama_C_dump_each();
            return ( 1 ); // EMBEDDED RETURN
          }
          else if ( ( direction == 0x00 ) && ( pRec->pCmdRecs[i].flag & 0x04 ) )
          {
            *pCmd = pRec->pCmdRecs[i];

            // Update command ID
            *pCmdID = pCmd->cmdID;
			Frama_C_dump_each();
            return ( 1 ); // EMBEDDED RETURN
          }
        }
        else if ( commandID == 0x13 )
        {
          if ( ( direction == 0x00 ) && ( pRec->pCmdRecs[i].flag & 0x01 ) )
          {
            *pCmd = pRec->pCmdRecs[i];

            // Update command ID
            *pCmdID = pCmd->cmdID;
			Frama_C_dump_each();
            return ( 1 ); // EMBEDDED RETURN
          }
          else if ( ( direction == 0x01 ) && ( pRec->pCmdRecs[i].flag & 0x02 ) )
          {
            *pCmd = pRec->pCmdRecs[i];

            // Update command ID
            *pCmdID = pCmd->cmdID;
			Frama_C_dump_each();
            return ( 1 ); // EMBEDDED RETURN
          }
        }
        else
        {
          Frama_C_dump_each();
		  return ( 0 ); // Incorrect Command ID
        }
      }
    }
  }
  Frama_C_dump_each();
  return ( 0 );
}

/*********************************************************************
 * @fn      zclFindNextAttrRec
 *
 * @brief   Find the attribute (or next) record that matchs the parameters
 *
 * @param   endpoint - Application's endpoint
 * @param   clusterID - cluster ID
 * @param   attr - attribute looking for
 *
 * @return  pointer to attribute record, NULL if not found
 */
static uint8 zclFindNextAttrRec( uint8 endpoint, uint16 clusterID, uint8 direction,
                                 uint16 *attrId, zclAttrRec_t *pAttr )
{
  zclAttrRecsList *pRec = zclFindAttrRecsList( endpoint );
  uint8 attrDir;

  if ( pRec != 0 )
  {
    uint16 x;

    for ( x = 0; x < pRec->numAttributes; x++ )
    {
      if ( ( pRec->attrs[x].clusterID == clusterID ) &&
           ( pRec->attrs[x].attr.attrId >= *attrId ) )
      {
        // also make sure direction is right
        attrDir = (pRec->attrs[x].attr.accessControl & 0x80) ? 1 : 0;
        if ( (attrDir == direction) || (pRec->attrs[x].attr.accessControl & 0x40))
        {
          // return attribute and found attribute ID
          *pAttr = pRec->attrs[x];
          *attrId = pAttr->attr.attrId;

		  Frama_C_dump_each();
          return ( 1 ); // EMBEDDED RETURN
        }
      }
    }
  }
  Frama_C_dump_each();
  return ( 0 );
}


/*********************************************************************
 * @fn      zclSerializeData
 *
 * @brief   Builds a buffer from the attribute data to sent out over
 *          the air.
 *          NOTE - Not compatible with application's attributes callbacks.
 *
 * @param   dataType - data types defined in zcl.h
 * @param   attrData - pointer to the attribute data
 * @param   buf - where to put the serialized data
 *
 * @return  pointer to end of destination buffer
 */
uint8 *zclSerializeData( uint8 dataType, void *attrData, uint8 *buf )
{
  uint8 *pStr;
  uint16 len;

  if ( attrData == 0 )
  {
    return ( buf );
  }

  switch ( dataType )
  {
    case 0x08:
    case 0x10:
    case 0x18:
    case 0x28:
    case 0x20:
    case 0x30:
      *buf++ = *((uint8 *)attrData);
       break;

    case 0x09:
    case 0x19:
    case 0x21:
    case 0x29:
    case 0x31:
    case 0x38:
    case 0xe8:
    case 0xe9:
      *buf++ = ((*((uint16*)attrData)) & 0xFF);
      *buf++ = (((*((uint16*)attrData)) >> 8) & 0xFF);
      break;

    case 0x0a:
    case 0x1a:
    case 0x22:
    case 0x2a:
      *buf++ = (uint8)((uint32)(((*((uint32*)attrData)) >>((0) * 8)) & 0x00FF));
      *buf++ = (uint8)((uint32)(((*((uint32*)attrData)) >>((1) * 8)) & 0x00FF));
      *buf++ = (uint8)((uint32)(((*((uint32*)attrData)) >>((2) * 8)) & 0x00FF));
      break;

    case 0x0b:
    case 0x1b:
    case 0x23:
    case 0x2b:
    case 0x39:
    case 0xe0:
    case 0xe1:
    case 0xe2:
    case 0xea:
      buf = osal_buffer_uint32( buf, *((uint32*)attrData) );
      break;

    case 0x24:
    case 0x2c:
      pStr = (uint8*)attrData;
      buf = osal_memcpy( buf, pStr, 5 );
      break;

    case 0x25:
    case 0x2d:
      pStr = (uint8*)attrData;
      buf = osal_memcpy( buf, pStr, 6 );
      break;

    case 0x26:
    case 0x2e:
      pStr = (uint8*)attrData;
      buf = osal_memcpy( buf, pStr, 7 );
      break;

    case 0x3a:
    case 0xf0:
    case 0x27:
    case 0x2f:
      pStr = (uint8*)attrData;
      buf = osal_memcpy( buf, pStr, 8 );
      break;

    case 0x42:
    case 0x41:
      pStr = (uint8*)attrData;
      len = *pStr;
      buf = osal_memcpy( buf, pStr, len+1 ); // Including length field
      break;

    case 0x44:
    case 0x43:
      pStr = (uint8*)attrData;
      len = ((uint16)(((pStr[0]) & 0x00FF) + (((pStr[1]) & 0x00FF) << 8)));
      buf = osal_memcpy( buf, pStr, len+2 ); // Including length field
      break;

    case 0xf1:
      pStr = (uint8*)attrData;
      buf = osal_memcpy( buf, pStr, 16 );
      break;

    case 0x00:
    case 0xff:
      // Fall through

    default:
      break;
  }
  Frama_C_dump_each();
  return ( buf );
}


/*********************************************************************
 * @fn      zclAnalogDataType
 *
 * @brief   Checks to see if Data Type is Analog
 *
 * @param   dataType - data type
 *
 * @return  TRUE if data type is analog
 */
uint8 zclAnalogDataType( uint8 dataType )
{
  uint8 analog;

  switch ( dataType )
  {
    case 0x20:
    case 0x21:
    case 0x22:
    case 0x23:
    case 0x24:
    case 0x25:
    case 0x26:
    case 0x27:
    case 0x28:
    case 0x29:
    case 0x2a:
    case 0x2b:
    case 0x2c:
    case 0x2d:
    case 0x2e:
    case 0x2f:
    case 0x38:
    case 0x39:
    case 0x3a:
    case 0xe0:
    case 0xe1:
    case 0xe2:
      analog = 1;
      break;

    default:
      analog = 0;
      break;
  }
  Frama_C_dump_each();
  return ( analog );
}

/*********************************************************************
 * @fn      zclIsLittleEndianMachine
 *
 * @brief   Verifies endianness in system.
 *
 * @param   none
 *
 * @return  MSB-00 or LSB-01 depending on endianness in the system
 */
static int zclIsLittleEndianMachine(void)
{
  uint16 test = 0x0001;

  return (*((uint8 *)(&test)));
}

/*********************************************************************
 * @fn      zcl_BuildAnalogData
 *
 * @brief   Build an analog arribute out of sequential bytes.
 *
 * @param   dataType - type of data
 * @param   pData - pointer to data
 * @param   pBuf - where to put the data
 *
 * @return  none
 */
static void zcl_BuildAnalogData( uint8 dataType, uint8 *pData, uint8 *pBuf )
{
  int current_byte_index;
  int remaining_bytes;
  int step;

  remaining_bytes = zclGetAttrDataLength(dataType, pData);

  // decide if move forward or backwards to copy data
  if ( zclIsLittleEndianMachine() )
  {
    step = 1;
    current_byte_index = 0;
  }
  else
  {
    step = -1;
    current_byte_index = remaining_bytes - 1;
  }

  while ( remaining_bytes-- )
  {
    pData[current_byte_index] = *(pBuf++);
    current_byte_index += step;
  }
  Frama_C_dump_each();
}


/*********************************************************************
 * @fn      zclGetDataTypeLength
 *
 * @brief   Return the length of the datatype in octet.
 *
 *          NOTE: Should not be called for ZCL_DATATYPE_OCTECT_STR or
 *                ZCL_DATATYPE_CHAR_STR data types.
 *
 * @param   dataType - data type
 *
 * @return  length of data
 */
uint8 zclGetDataTypeLength( uint8 dataType )
{
  uint8 len;

  switch ( dataType )
  {
    case 0x08:
    case 0x10:
    case 0x18:
    case 0x28:
    case 0x20:
    case 0x30:
      len = 1;
      break;

    case 0x09:
    case 0x19:
    case 0x21:
    case 0x29:
    case 0x31:
    case 0x38:
    case 0xe8:
    case 0xe9:
      len = 2;
      break;

    case 0x0a:
    case 0x1a:
    case 0x22:
    case 0x2a:
      len = 3;
      break;

    case 0x0b:
    case 0x1b:
    case 0x23:
    case 0x2b:
    case 0x39:
    case 0xe0:
    case 0xe1:
    case 0xe2:
    case 0xea:
      len = 4;
      break;

   case 0x24:
   case 0x2c:
       len = 5;
       break;

   case 0x25:
   case 0x2d:
       len = 6;
       break;

   case 0x26:
   case 0x2e:
       len = 7;
       break;

   case 0x3a:
   case 0xf0:
   case 0x27:
   case 0x2f:
     len = 8;
     break;

    case 0xf1:
     len = 16;
     break;

    case 0x00:
    case 0xff:
      // Fall through

    default:
      len = 0;
      break;
  }
  Frama_C_dump_each();
  return ( len );
}

/*********************************************************************
 * @fn      zclGetAttrDataLength
 *
 * @brief   Return the length of the attribute.
 *
 * @param   dataType - data type
 * @param   pData - pointer to data
 *
 * @return  returns atrribute length
 */
uint16 zclGetAttrDataLength( uint8 dataType, uint8 *pData )
{
  uint16 dataLen = 0;

  if ( dataType == 0x44 || dataType == 0x43 )
  {
    dataLen = ((uint16)(((pData[0]) & 0x00FF) + (((pData[1]) & 0x00FF) << 8))) + 2; // long string length + 2 for length field
  }
  else if ( dataType == 0x42 || dataType == 0x41 )
  {
    dataLen = *pData + 1; // string length + 1 for length field
  }
  else
  {
    dataLen = zclGetDataTypeLength( dataType );
  }
  Frama_C_dump_each();
  return ( dataLen );
}


/*********************************************************************
 * @fn      zclReadAttrData
 *
 * @brief   Read the attribute's current value into pAttrData.
 *          NOTE - Not compatible with application's attributes callbacks.
 *
 * @param   pAttrData - where to put attribute data
 * @param   pAttr - pointer to attribute
 * @param   pDataLen - where to put attribute data length
 *
 * @return Success
 */
ZStatus_t zclReadAttrData( uint8 *pAttrData, zclAttrRec_t *pAttr, uint16 *pDataLen )
{
  uint16 dataLen;

  if ( pAttr->attr.dataPtr == 0 )
  {
    return ( 0x01 );
  }

  dataLen = zclGetAttrDataLength( pAttr->attr.dataType, (uint8*)(pAttr->attr.dataPtr) );
  osal_memcpy( pAttrData, pAttr->attr.dataPtr, dataLen );

  if ( pDataLen != 0 )
  {
    *pDataLen = dataLen;
  }
  Frama_C_dump_each();
  return ( 0x00 );
}

/*********************************************************************
 * @fn      zcl_ReadAttrData
 *
 * @brief   Read the attribute's current value into pAttrData.
 *          Use application's callback function if assigned to this attribute.
 *
 * @param   endpoint - application's endpoint
 * @param   clusterId - cluster that attribute belongs to
 * @param   attrId - attribute id
 * @param   pAttrData - where to put attribute data
 * @param   pDataLen - where to put attribute data length
 *
 * @return  Successful if data was read
 */
ZStatus_t zcl_ReadAttrData( uint8 endpoint, uint16 clusterId, uint16 attrId,
                                         uint8 *pAttrData, uint16 *pDataLen )
{
  zclAttrRec_t attrRec;

  if ( zclFindAttrRec( endpoint, clusterId, attrId, &attrRec ) == 0 )
  {
    Frama_C_dump_each();
	return ( 0x01 );
  }

  if ( attrRec.attr.dataPtr != 0 )
  {
    Frama_C_dump_each();
	return zclReadAttrData( pAttrData, &attrRec, pDataLen );
  }
  else
  {
    Frama_C_dump_each();
	return zclReadAttrDataUsingCB( endpoint, clusterId, attrId, pAttrData, pDataLen );
  }
}

/*********************************************************************
 * @fn      zclGetAttrDataLengthUsingCB
 *
 * @brief   Use application's callback to get the length of the attribute's
 *          current value stored in the database.
 *
 * @param   endpoint - application's endpoint
 * @param   clusterId - cluster that attribute belongs to
 * @param   attrId - attribute id
 *
 * @return  returns attribute length
 */
static uint16 zclGetAttrDataLengthUsingCB( uint8 endpoint, uint16 clusterId, uint16 attrId )
{
  uint16 dataLen = 0;
  zclReadWriteCB_t pfnReadWriteCB = zclGetReadWriteCB( endpoint );

  if ( pfnReadWriteCB != 0 )
  {
    // Only get the attribute length
    (*pfnReadWriteCB)( clusterId, attrId, 0x00, 0, &dataLen );
  }
  Frama_C_dump_each();
  return ( dataLen );
}

/*********************************************************************
 * @fn      zclReadAttrDataUsingCB
 *
 * @brief   Use application's callback to read the attribute's current
 *          value stored in the database.
 *
 * @param   endpoint - application's endpoint
 * @param   clusterId - cluster that attribute belongs to
 * @param   attrId - attribute id
 * @param   pAttrData - where to put attribute data
 * @param   pDataLen - where to put attribute data length
 *
 * @return  Successful if data was read
 */
static ZStatus_t zclReadAttrDataUsingCB( uint8 endpoint, uint16 clusterId, uint16 attrId,
                                         uint8 *pAttrData, uint16 *pDataLen )
{
  zclReadWriteCB_t pfnReadWriteCB = zclGetReadWriteCB( endpoint );

  if ( pDataLen != 0 )
  {
    *pDataLen = 0; // Always initialize it to 0
  }

  if ( pfnReadWriteCB != 0 )
  {
    // Read the attribute value and its length
    return ( (*pfnReadWriteCB)( clusterId, attrId, 0x01, pAttrData, pDataLen ) );
  }
  Frama_C_dump_each();
  return ( 0xc1 );
}

/*********************************************************************
 * @fn      zclAuthorizeRead
 *
 * @brief   Use application's callback to authorize a Read operation
 *          on a given attribute.
 *
 * @param   endpoint - application's endpoint
 * @param   srcAddr - source Address
 * @param   pAttr - pointer to attribute
 *
 * @return  ZCL_STATUS_SUCCESS: Operation authorized
 *          ZCL_STATUS_NOT_AUTHORIZED: Operation not authorized
 */
static ZStatus_t zclAuthorizeRead( uint8 endpoint, afAddrType_t *srcAddr, zclAttrRec_t *pAttr )
{
  if ( ( (pAttr->attr . accessControl) & 0x10 ) )
  {
    zclAuthorizeCB_t pfnAuthorizeCB = zclGetAuthorizeCB( endpoint );

    if ( pfnAuthorizeCB != 0 )
    {
      return ( (*pfnAuthorizeCB)( srcAddr, pAttr, 0x01 ) );
    }
  }
  Frama_C_dump_each();
  return ( 0x00 );
}



/*********************************************************************
 * @fn      zclWriteAttrData
 *
 * @brief   Write the received data.
 *
 * @param   endpoint - application's endpoint
 * @param   pAttr - where to write data to
 * @param   pWriteRec - data to be written
 *
 * @return  Successful if data was written
 */
static ZStatus_t zclWriteAttrData( uint8 endpoint, afAddrType_t *srcAddr,
                                   zclAttrRec_t *pAttr, zclWriteRec_t *pWriteRec )
{
  uint8 status;

  if ( ( (pAttr->attr . accessControl) & 0x02 ) )
  {
    status = zclAuthorizeWrite( endpoint, srcAddr, pAttr );
    if ( status == 0x00 )
    {
      if ( ( zcl_ValidateAttrDataCB == 0 ) || zcl_ValidateAttrDataCB( pAttr, pWriteRec ) )
      {
        // Write the attribute value
        uint16 len = zclGetAttrDataLength( pAttr->attr.dataType, pWriteRec->attrData );
        osal_memcpy( pAttr->attr.dataPtr, pWriteRec->attrData, len );

        status = 0x00;
      }
      else
      {
        status = 0x87;
      }
    }
  }
  else
  {
    status = 0x88;
  }
  Frama_C_dump_each();
  return ( status );
}

/*********************************************************************
 * @fn      zclWriteAttrDataUsingCB
 *
 * @brief   Use application's callback to write the attribute's current
 *          value stored in the database.
 *
 * @param   endpoint - application's endpoint
 * @param   pAttr - where to write data to
 * @param   pAttrData - data to be written
 *
 * @return  Successful if data was written
 */
static ZStatus_t zclWriteAttrDataUsingCB( uint8 endpoint, afAddrType_t *srcAddr,
                                          zclAttrRec_t *pAttr, uint8 *pAttrData )
{
  uint8 status;

  if ( ( (pAttr->attr . accessControl) & 0x02 ) )
  {
    status = zclAuthorizeWrite( endpoint, srcAddr, pAttr );
    if ( status == 0x00 )
    {
      zclReadWriteCB_t pfnReadWriteCB = zclGetReadWriteCB( endpoint );
      if ( pfnReadWriteCB != 0 )
      {
        // Write the attribute value
        status = (*pfnReadWriteCB)( pAttr->clusterID, pAttr->attr.attrId,
                                    0x02, pAttrData, 0 );
      }
      else
      {
        status = 0xc1;
      }
    }
  }
  else
  {
    status = 0x88;
  }
  Frama_C_dump_each();
  return ( status );
}

/*********************************************************************
 * @fn      zclAuthorizeWrite
 *
 * @brief   Use application's callback to authorize a Write operation
 *          on a given attribute.
 *
 * @param   endpoint - application's endpoint
 * @param   srcAddr - source Address
 * @param   pAttr - pointer to attribute
 *
 * @return  ZCL_STATUS_SUCCESS: Operation authorized
 *          ZCL_STATUS_NOT_AUTHORIZED: Operation not authorized
 */
static ZStatus_t zclAuthorizeWrite( uint8 endpoint, afAddrType_t *srcAddr, zclAttrRec_t *pAttr )
{
  if ( ( (pAttr->attr . accessControl) & 0x20 ) )
  {
    zclAuthorizeCB_t pfnAuthorizeCB = zclGetAuthorizeCB( endpoint );

    if ( pfnAuthorizeCB != 0 )
    {
	  Frama_C_dump_each();
      return ( (*pfnAuthorizeCB)( srcAddr, pAttr, 0x02 ) );
    }
  }
  Frama_C_dump_each();
  return ( 0x00 );
}



/*********************************************************************
 * @fn      zclParseInReadCmd
 *
 * @brief   Parse the "Profile" Read Commands
 *
 *      NOTE: THIS FUNCTION ALLOCATES THE RETURN BUFFER, SO THE CALLING
 *            FUNCTION IS RESPONSIBLE TO FREE THE MEMORY.
 *
 * @param   pCmd - pointer to incoming data to parse
 *
 * @return  pointer to the parsed command structure
 */
void *zclParseInReadCmd( zclParseCmd_t *pCmd )
{
  zclReadCmd_t *readCmd;
  uint8 *pBuf = pCmd->pData;
  
  readCmd = (zclReadCmd_t *)osal_mem_alloc( sizeof ( zclReadCmd_t ) + pCmd->dataLen );
  
  if ( readCmd != 0 )
  {
    uint8 i;
    readCmd->numAttr = pCmd->dataLen / 2; // Atrribute ID
    for ( i = 0; i < readCmd->numAttr; i++ )
    {
      readCmd->attrID[i] = ((uint16)(((pBuf[0]) & 0x00FF) + (((pBuf[1]) & 0x00FF) << 8)));
      pBuf += 2;
    }
  }
  Frama_C_dump_each();
  return ( (void *)readCmd );
}

/*********************************************************************
 * @fn      zclParseInReadRspCmd
 *
 * @brief   Parse the "Profile" Read Response Commands
 *
 *      NOTE: THIS FUNCTION ALLOCATES THE RETURN BUFFER, SO THE CALLING
 *            FUNCTION IS RESPONSIBLE TO FREE THE MEMORY.
 *
 * @param   pCmd - pointer to incoming data to parse
 *
 * @return  pointer to the parsed command structure
 */
static void *zclParseInReadRspCmd( zclParseCmd_t *pCmd )
{
  zclReadRspCmd_t *readRspCmd;
  uint8 *pBuf = pCmd->pData;
  uint8 *dataPtr;
  uint8 numAttr = 0;
  uint8 hdrLen;
  uint16 dataLen = 0;
  uint16 attrDataLen;

  // find out the number of attributes and the length of attribute data
  while ( pBuf < ( pCmd->pData + pCmd->dataLen ) )
  {
    uint8 status;

    numAttr++;
    pBuf += 2; // move pass attribute id

    status = *pBuf++;
    if ( status == 0x00 )
    {
      uint8 dataType = *pBuf++;

      attrDataLen = zclGetAttrDataLength( dataType, pBuf );
      pBuf += attrDataLen; // move pass attribute data

      // add padding if needed
      if ( ( (attrDataLen) % 2 ) )
      {
        attrDataLen++;
      }

      dataLen += attrDataLen;
    }
  }
  Frama_C_dump_each();
  // calculate the length of the response header
  hdrLen = sizeof( zclReadRspCmd_t ) + ( numAttr * sizeof( zclReadRspStatus_t ) );

  readRspCmd = (zclReadRspCmd_t *)osal_mem_alloc( hdrLen + dataLen );
  if ( readRspCmd != 0 )
  {
    uint8 i;
    pBuf = pCmd->pData;
    dataPtr = (uint8 *)( (uint8 *)readRspCmd + hdrLen );
    readRspCmd->numAttr = numAttr;
    for ( i = 0; i < numAttr; i++ )
    {
      zclReadRspStatus_t *statusRec = &(readRspCmd->attrList[i]);

      statusRec->attrID = ((uint16)(((pBuf[0]) & 0x00FF) + (((pBuf[1]) & 0x00FF) << 8)));
      pBuf += 2;

      statusRec->status = *pBuf++;
      if ( statusRec->status == 0x00 )
      {
        statusRec->dataType = *pBuf++;

        attrDataLen = zclGetAttrDataLength( statusRec->dataType, pBuf );
        osal_memcpy( dataPtr, pBuf, attrDataLen);
        statusRec->data = dataPtr;

        pBuf += attrDataLen; // move pass attribute data

        // advance attribute data pointer
        if ( ( (attrDataLen) % 2 ) )
        {
          attrDataLen++;
        }

        dataPtr += attrDataLen;
      }
    }
  }
  Frama_C_dump_each();
  return ( (void *)readRspCmd );
}



/*********************************************************************
 * @fn      zclParseInWriteCmd
 *
 * @brief   Parse the "Profile" Write, Write Undivided and Write No
 *          Response Commands
 *
 *      NOTE: THIS FUNCTION ALLOCATES THE RETURN BUFFER, SO THE CALLING
 *            FUNCTION IS RESPONSIBLE TO FREE THE MEMORY.
 *
 * @param   pCmd - pointer to incoming data to parse
 *
 * @return  pointer to the parsed command structure
 */
void *zclParseInWriteCmd( zclParseCmd_t *pCmd )
{
  zclWriteCmd_t *writeCmd;
  uint8 *pBuf = pCmd->pData;
  uint16 attrDataLen;
  uint8 *dataPtr;
  uint8 numAttr = 0;
  uint8 hdrLen;
  uint16 dataLen = 0;

  // find out the number of attributes and the length of attribute data
  while ( pBuf < ( pCmd->pData + pCmd->dataLen ) )
  {
    uint8 dataType;

    numAttr++;
    pBuf += 2; // move pass attribute id

    dataType = *pBuf++;

    attrDataLen = zclGetAttrDataLength( dataType, pBuf );
    pBuf += attrDataLen; // move pass attribute data

    // add padding if needed
    if ( ( (attrDataLen) % 2 ) )
    {
      attrDataLen++;
    }

    dataLen += attrDataLen;
  }

  // calculate the length of the response header
  hdrLen = sizeof( zclWriteCmd_t ) + ( numAttr * sizeof( zclWriteRec_t ) );

  writeCmd = (zclWriteCmd_t *)osal_mem_alloc( hdrLen + dataLen );
  if ( writeCmd != 0 )
  {
    uint8 i;
    pBuf = pCmd->pData;
    dataPtr = (uint8 *)( (uint8 *)writeCmd + hdrLen );

    writeCmd->numAttr = numAttr;
    for ( i = 0; i < numAttr; i++ )
    {
      zclWriteRec_t *statusRec = &(writeCmd->attrList[i]);

      statusRec->attrID = ((uint16)(((pBuf[0]) & 0x00FF) + (((pBuf[1]) & 0x00FF) << 8)));
      pBuf += 2;
      statusRec->dataType = *pBuf++;

      attrDataLen = zclGetAttrDataLength( statusRec->dataType, pBuf );
      osal_memcpy( dataPtr, pBuf, attrDataLen);
      statusRec->attrData = dataPtr;

      pBuf += attrDataLen; // move pass attribute data

      // advance attribute data pointer
      if ( ( (attrDataLen) % 2 ) )
      {
        attrDataLen++;
      }

      dataPtr += attrDataLen;
    }
  }
  Frama_C_dump_each();
  return ( (void *)writeCmd );
}

/*********************************************************************
 * @fn      zclParseInWriteRspCmd
 *
 * @brief   Parse the "Profile" Write Response Commands
 *
 *      NOTE: THIS FUNCTION ALLOCATES THE RETURN BUFFER, SO THE CALLING
 *            FUNCTION IS RESPONSIBLE TO FREE THE MEMORY.
 *
 * @param   pCmd - pointer to incoming data to parse
 *
 * @return  pointer to the parsed command structure
 */
static void *zclParseInWriteRspCmd( zclParseCmd_t *pCmd )
{
  zclWriteRspCmd_t *writeRspCmd;
  uint8 *pBuf = pCmd->pData;
  uint8 i = 0;

  writeRspCmd = (zclWriteRspCmd_t *)osal_mem_alloc( sizeof ( zclWriteRspCmd_t ) + pCmd->dataLen );
  if ( writeRspCmd != 0 )
  {
    if ( pCmd->dataLen == 1 )
    {
      // special case when all writes were successfull
      writeRspCmd->attrList[i++].status = *pBuf;
    }
    else
    {
      while ( pBuf < ( pCmd->pData + pCmd->dataLen ) )
      {
        writeRspCmd->attrList[i].status = *pBuf++;
        writeRspCmd->attrList[i++].attrID = ((uint16)(((pBuf[0]) & 0x00FF) + (((pBuf[1]) & 0x00FF) << 8)));
        pBuf += 2;
      }
    }

    writeRspCmd->numAttr = i;
  }
  Frama_C_dump_each();
  return ( (void *)writeRspCmd );
}



/*********************************************************************
 * @fn      zclParseInConfigReportCmd
 *
 * @brief   Parse the "Profile" Configure Reporting Command
 *
 *      NOTE: THIS FUNCTION ALLOCATES THE RETURN BUFFER, SO THE CALLING
 *            FUNCTION IS RESPONSIBLE TO FREE THE MEMORY.
 *
 * @param   pCmd - pointer to incoming data to parse
 *
 * @return  pointer to the parsed command structure
 */
void *zclParseInConfigReportCmd( zclParseCmd_t *pCmd )
{
  zclCfgReportCmd_t *cfgReportCmd;
  uint8 *pBuf = pCmd->pData;
  uint8 *dataPtr;
  uint8 numAttr = 0;
  uint8 dataType;
  uint8 hdrLen;
  uint16 dataLen = 0;
  uint8 reportChangeLen; // length of Reportable Change field

  // Calculate the length of the Request command
  while ( pBuf < ( pCmd->pData + pCmd->dataLen ) )
  {
    uint8 direction;

    numAttr++;
    direction = *pBuf++;
    pBuf += 2; // move pass the attribute ID

    // Is there a Reportable Change field?
    if ( direction == 0x00 )
    {
      dataType = *pBuf++;
      pBuf += 4; // move pass the Min and Max Reporting Intervals

      // For attributes of 'discrete' data types this field is omitted
      if ( zclAnalogDataType( dataType ) )
      {
        reportChangeLen = zclGetDataTypeLength( dataType );
        pBuf += reportChangeLen;

        // add padding if needed
        if ( ( (reportChangeLen) % 2 ) )
        {
          reportChangeLen++;
        }

        dataLen += reportChangeLen;
      }
      else
      {
        pBuf++; // move past reportable change field
      }
    }
    else
    {
      pBuf += 2; // move pass the Timeout Period
    }
  } // while loop

  hdrLen = sizeof( zclCfgReportCmd_t ) + ( numAttr * sizeof( zclCfgReportRec_t ) );

  cfgReportCmd = (zclCfgReportCmd_t *)osal_mem_alloc( hdrLen + dataLen );
  if ( cfgReportCmd != 0 )
  {
    uint8 i;
    pBuf = pCmd->pData;
    dataPtr = (uint8 *)( (uint8 *)cfgReportCmd + hdrLen );

    cfgReportCmd->numAttr = numAttr;
    for ( i = 0; i < numAttr; i++ )
    {
      zclCfgReportRec_t *reportRec = &(cfgReportCmd->attrList[i]);

      osal_memset( reportRec, 0, sizeof( zclCfgReportRec_t ) );

      reportRec->direction = *pBuf++;
      reportRec->attrID = ((uint16)(((pBuf[0]) & 0x00FF) + (((pBuf[1]) & 0x00FF) << 8)));
      pBuf += 2;
      if ( reportRec->direction == 0x00 )
      {
        // Attribute to be reported
        reportRec->dataType = *pBuf++;
        reportRec->minReportInt = ((uint16)(((pBuf[0]) & 0x00FF) + (((pBuf[1]) & 0x00FF) << 8)));
        pBuf += 2;
        reportRec->maxReportInt = ((uint16)(((pBuf[0]) & 0x00FF) + (((pBuf[1]) & 0x00FF) << 8)));
        pBuf += 2;

        // For attributes of 'discrete' data types this field is omitted
        if ( zclAnalogDataType( reportRec->dataType ) )
        {
          zcl_BuildAnalogData( reportRec->dataType, dataPtr, pBuf);
          reportRec->reportableChange = dataPtr;

          reportChangeLen = zclGetDataTypeLength( reportRec->dataType );
          pBuf += reportChangeLen;

          // advance attribute data pointer
          if ( ( (reportChangeLen) % 2 ) )
          {
            reportChangeLen++;
          }

          dataPtr += reportChangeLen;
        }
      }
      else
      {
        // Attribute reports to be received
        reportRec->timeoutPeriod = ((uint16)(((pBuf[0]) & 0x00FF) + (((pBuf[1]) & 0x00FF) << 8)));
        pBuf += 2;
      }
    } // while loop
  }
  Frama_C_dump_each();
  return ( (void *)cfgReportCmd );
}



/*********************************************************************
 * @fn      zclParseInConfigReportRspCmd
 *
 * @brief   Parse the "Profile" Configure Reporting Response Command
 *
 *      NOTE: THIS FUNCTION ALLOCATES THE RETURN BUFFER, SO THE CALLING
 *            FUNCTION IS RESPONSIBLE TO FREE THE MEMORY.
 *
 * @param   pCmd - pointer to incoming data to parse
 *
 * @return  pointer to the parsed command structure
 */
static void *zclParseInConfigReportRspCmd( zclParseCmd_t *pCmd )
{
  zclCfgReportRspCmd_t *cfgReportRspCmd;
  uint8 *pBuf = pCmd->pData;
  uint8 numAttr;

  numAttr = pCmd->dataLen / ( 1 + 1 + 2 ); // Status + Direction + Attribute ID

  cfgReportRspCmd = (zclCfgReportRspCmd_t *)osal_mem_alloc( sizeof( zclCfgReportRspCmd_t )
                                            + ( numAttr * sizeof( zclCfgReportStatus_t ) ) );
  if ( cfgReportRspCmd != 0 )
  {
    uint8 i;
    cfgReportRspCmd->numAttr = numAttr;
    for ( i = 0; i < cfgReportRspCmd->numAttr; i++ )
    {
      cfgReportRspCmd->attrList[i].status = *pBuf++;
      cfgReportRspCmd->attrList[i].direction = *pBuf++;
      cfgReportRspCmd->attrList[i].attrID = ((uint16)(((pBuf[0]) & 0x00FF) + (((pBuf[1]) & 0x00FF) << 8)));
      pBuf += 2;
    }
  }
  Frama_C_dump_each();
  return ( (void *)cfgReportRspCmd );
}



/*********************************************************************
 * @fn      zclParseInReadReportCfgCmd
 *
 * @brief   Parse the "Profile" Read Reporting Configuration Command
 *
 *      NOTE: THIS FUNCTION ALLOCATES THE RETURN BUFFER, SO THE CALLING
 *            FUNCTION IS RESPONSIBLE TO FREE THE MEMORY.
 *
 * @param   pCmd - pointer to incoming data to parse
 *
 * @return  pointer to the parsed command structure
 */
void *zclParseInReadReportCfgCmd( zclParseCmd_t *pCmd )
{
  zclReadReportCfgCmd_t *readReportCfgCmd;
  uint8 *pBuf = pCmd->pData;
  uint8 numAttr;

  numAttr = pCmd->dataLen / ( 1 + 2 ); // Direction + Attribute ID

  readReportCfgCmd = (zclReadReportCfgCmd_t *)osal_mem_alloc( sizeof( zclReadReportCfgCmd_t )
                                                  + ( numAttr * sizeof( zclReadReportCfgRec_t ) ) );
  if ( readReportCfgCmd != 0 )
  {
    uint8 i;
    readReportCfgCmd->numAttr = numAttr;
    for ( i = 0; i < readReportCfgCmd->numAttr; i++)
    {
      readReportCfgCmd->attrList[i].direction = *pBuf++;;
      readReportCfgCmd->attrList[i].attrID = ((uint16)(((pBuf[0]) & 0x00FF) + (((pBuf[1]) & 0x00FF) << 8)));
      pBuf += 2;
    }
  }
  Frama_C_dump_each();
  return ( (void *)readReportCfgCmd );
}



/*********************************************************************
 * @fn      zclParseInReadReportCfgRspCmd
 *
 * @brief   Parse the "Profile" Read Reporting Configuration Response Command
 *
 *      NOTE: THIS FUNCTION ALLOCATES THE RETURN BUFFER, SO THE CALLING
 *            FUNCTION IS RESPONSIBLE TO FREE THE MEMORY.
 *
 * @param   pCmd - pointer to incoming data to parse
 *
 * @return  pointer to the parsed command structure
 */
static void *zclParseInReadReportCfgRspCmd( zclParseCmd_t *pCmd )
{
  zclReadReportCfgRspCmd_t *readReportCfgRspCmd;
  uint8 reportChangeLen;
  uint8 *pBuf = pCmd->pData;
  uint8 *dataPtr;
  uint8 numAttr = 0;
  uint8 hdrLen;
  uint16 dataLen = 0;

  // Calculate the length of the response command
  while ( pBuf < ( pCmd->pData + pCmd->dataLen ) )
  {
    uint8 status;
    uint8 direction;

    numAttr++;
    status = *pBuf++;
    direction = *pBuf++;
    pBuf += 2; // move pass the attribute ID

    if ( status == 0x00 )
    {
      if ( direction == 0x00 )
      {
        uint8 dataType = *pBuf++;
        pBuf += 4; // move pass the Min and Max Reporting Intervals

        // For attributes of 'discrete' data types this field is omitted
        if ( zclAnalogDataType( dataType ) )
        {
          reportChangeLen = zclGetDataTypeLength( dataType );
          pBuf += reportChangeLen;

          // add padding if needed
          if ( ( (reportChangeLen) % 2 ) )
          {
            reportChangeLen++;
          }

          dataLen += reportChangeLen;
        }
      }
      else
      {
        pBuf += 2; // move pass the Timeout field
      }
    }
  } // while loop

  hdrLen = sizeof( zclReadReportCfgRspCmd_t ) + ( numAttr * sizeof( zclReportCfgRspRec_t ) );

  readReportCfgRspCmd = (zclReadReportCfgRspCmd_t *)osal_mem_alloc( hdrLen + dataLen );
  if ( readReportCfgRspCmd != 0 )
  {
    uint8 i;
    pBuf = pCmd->pData;
    dataPtr = (uint8 *)( (uint8 *)readReportCfgRspCmd + hdrLen );

    readReportCfgRspCmd->numAttr = numAttr;
    for ( i = 0; i < numAttr; i++ )
    {
      zclReportCfgRspRec_t *reportRspRec = &(readReportCfgRspCmd->attrList[i]);

      reportRspRec->status = *pBuf++;
      reportRspRec->direction = *pBuf++;
      reportRspRec->attrID = ((uint16)(((pBuf[0]) & 0x00FF) + (((pBuf[1]) & 0x00FF) << 8)));
      pBuf += 2;

      if ( reportRspRec->status == 0x00 )
      {
        if ( reportRspRec->direction == 0x00 )
        {
          reportRspRec->dataType = *pBuf++;
          reportRspRec->minReportInt = ((uint16)(((pBuf[0]) & 0x00FF) + (((pBuf[1]) & 0x00FF) << 8)));
          pBuf += 2;
          reportRspRec->maxReportInt = ((uint16)(((pBuf[0]) & 0x00FF) + (((pBuf[1]) & 0x00FF) << 8)));
          pBuf += 2;

          if ( zclAnalogDataType( reportRspRec->dataType ) )
          {
            zcl_BuildAnalogData( reportRspRec->dataType, dataPtr, pBuf);
            reportRspRec->reportableChange = dataPtr;

            reportChangeLen = zclGetDataTypeLength( reportRspRec->dataType );
            pBuf += reportChangeLen;

            // advance attribute data pointer
            if ( ( (reportChangeLen) % 2 ) )
            {
              reportChangeLen++;
            }

            dataPtr += reportChangeLen;
          }
        }
        else
        {
          reportRspRec->timeoutPeriod = ((uint16)(((pBuf[0]) & 0x00FF) + (((pBuf[1]) & 0x00FF) << 8)));
          pBuf += 2;
        }
      }
    }
  }
  Frama_C_dump_each();
  return ( (void *)readReportCfgRspCmd );
}



/*********************************************************************
 * @fn      zclParseInReportCmd
 *
 * @brief   Parse the "Profile" Report Command
 *
 *      NOTE: THIS FUNCTION ALLOCATES THE RETURN BUFFER, SO THE CALLING
 *            FUNCTION IS RESPONSIBLE TO FREE THE MEMORY.
 *
 * @param   pCmd - pointer to incoming data to parse
 *
 * @return  pointer to the parsed command structure
 */
void *zclParseInReportCmd( zclParseCmd_t *pCmd )
{
  zclReportCmd_t *reportCmd;
  uint8 *pBuf = pCmd->pData;
  uint16 attrDataLen;
  uint8 *dataPtr;
  uint8 numAttr = 0;
  uint8 hdrLen;
  uint16 dataLen = 0;

  // find out the number of attributes and the length of attribute data
  while ( pBuf < ( pCmd->pData + pCmd->dataLen ) )
  {
    uint8 dataType;

    numAttr++;
    pBuf += 2; // move pass attribute id

    dataType = *pBuf++;

    attrDataLen = zclGetAttrDataLength( dataType, pBuf );
    pBuf += attrDataLen; // move pass attribute data

    // add padding if needed
    if ( ( (attrDataLen) % 2 ) )
    {
      attrDataLen++;
    }

    dataLen += attrDataLen;
  }

  hdrLen = sizeof( zclReportCmd_t ) + ( numAttr * sizeof( zclReport_t ) );

  reportCmd = (zclReportCmd_t *)osal_mem_alloc( hdrLen + dataLen );
  if (reportCmd != 0 )
  {
    uint8 i;
    pBuf = pCmd->pData;
    dataPtr = (uint8 *)( (uint8 *)reportCmd + hdrLen );

    reportCmd->numAttr = numAttr;
    for ( i = 0; i < numAttr; i++ )
    {
      zclReport_t *reportRec = &(reportCmd->attrList[i]);

      reportRec->attrID = ((uint16)(((pBuf[0]) & 0x00FF) + (((pBuf[1]) & 0x00FF) << 8)));
      pBuf += 2;
      reportRec->dataType = *pBuf++;

      attrDataLen = zclGetAttrDataLength( reportRec->dataType, pBuf );
      osal_memcpy( dataPtr, pBuf, attrDataLen );
      reportRec->attrData = dataPtr;

      pBuf += attrDataLen; // move pass attribute data

      // advance attribute data pointer
      if ( ( (attrDataLen) % 2 ) )
      {
        attrDataLen++;
      }

      dataPtr += attrDataLen;
    }
  }
  Frama_C_dump_each();
  return ( (void *)reportCmd );
}


/*********************************************************************
 * @fn      zclParseInDefaultRspCmd
 *
 * @brief   Parse the "Profile" Default Response Command
 *
 *      NOTE: THIS FUNCTION ALLOCATES THE RETURN BUFFER, SO THE CALLING
 *            FUNCTION IS RESPONSIBLE TO FREE THE MEMORY.
 *
 * @param   pCmd - pointer to incoming data to parse
 *
 * @return  pointer to the parsed command structure
 */
static void *zclParseInDefaultRspCmd( zclParseCmd_t *pCmd )
{
  zclDefaultRspCmd_t *defaultRspCmd;
  uint8 *pBuf = pCmd->pData;

  defaultRspCmd = (zclDefaultRspCmd_t *)osal_mem_alloc( sizeof ( zclDefaultRspCmd_t ) );
  if ( defaultRspCmd != 0 )
  {
    defaultRspCmd->commandID = *pBuf++;
    defaultRspCmd->statusCode = *pBuf;
  }
  Frama_C_dump_each();
  return ( (void *)defaultRspCmd );
}


/*********************************************************************
 * @fn      zclParseInDiscAttrsCmd
 *
 * @brief   Parse the "Profile" Discovery Attributes and Attributes Extended Commands
 *
 *      NOTE: THIS FUNCTION ALLOCATES THE RETURN BUFFER, SO THE CALLING
 *            FUNCTION IS RESPONSIBLE TO FREE THE MEMORY.
 *
 * @param   pCmd - pointer to incoming data to parse
 *
 * @return  pointer to the parsed command structure
 */
void *zclParseInDiscAttrsCmd( zclParseCmd_t *pCmd )
{
  zclDiscoverAttrsCmd_t *pDiscoverCmd;
  uint8 *pBuf = pCmd->pData;

  pDiscoverCmd = (zclDiscoverAttrsCmd_t *)osal_mem_alloc( sizeof ( zclDiscoverAttrsCmd_t ) );
  if ( pDiscoverCmd != 0 )
  {
    pDiscoverCmd->startAttr = ((uint16)(((pBuf[0]) & 0x00FF) + (((pBuf[1]) & 0x00FF) << 8)));
    pBuf += 2;
    pDiscoverCmd->maxAttrIDs = *pBuf;
  }
  Frama_C_dump_each();
  return ( (void *)pDiscoverCmd );
}

/*********************************************************************
 * @fn      zclParseInDiscAttrsRspCmd
 *
 * @brief   Parse the "Profile" Discovery Response Commands
 *
 *      NOTE: THIS FUNCTION ALLOCATES THE RETURN BUFFER, SO THE CALLING
 *            FUNCTION IS RESPONSIBLE TO FREE THE MEMORY.
 *
 * @param   pCmd - pointer to incoming data to parse
 *
 * @return  pointer to the parsed command structure
 */

static void *zclParseInDiscAttrsRspCmd( zclParseCmd_t *pCmd )
{
  zclDiscoverAttrsRspCmd_t *pDiscoverRspCmd;
  uint8 *pBuf = pCmd->pData;
  uint8 numAttr = ((pCmd->dataLen)-1) / ( 2 + 1 ); // Attr ID + Data Type

  pDiscoverRspCmd = (zclDiscoverAttrsRspCmd_t *)osal_mem_alloc( sizeof ( zclDiscoverAttrsRspCmd_t ) +
                    ( numAttr * sizeof(zclDiscoverAttrInfo_t) ) );

  if ( pDiscoverRspCmd != 0 )
  {
    uint8 i;

    pDiscoverRspCmd->discComplete = *pBuf++;
    pDiscoverRspCmd->numAttr = numAttr;

    for ( i = 0; i < numAttr; i++ )
    {
      pDiscoverRspCmd->attrList[i].attrID = ((uint16)(((pBuf[0]) & 0x00FF) + (((pBuf[1]) & 0x00FF) << 8)));
      pBuf += 2;
      pDiscoverRspCmd->attrList[i].dataType = *pBuf++;
    }
  }
  Frama_C_dump_each();
  return ( (void *)pDiscoverRspCmd );
}

/*********************************************************************
 * @fn      zclParseInDiscCmdsCmd
 *
 * @brief   Parse the "Profile" Discovery Commands
 *
 *      NOTE: THIS FUNCTION ALLOCATES THE RETURN BUFFER, SO THE CALLING
 *            FUNCTION IS RESPONSIBLE TO FREE THE MEMORY.
 *
 * @param   pCmd - pointer to incoming data to parse
 *
 * @return  pointer to the parsed command structure
 */
void *zclParseInDiscCmdsCmd( zclParseCmd_t *pCmd )
{
  zclDiscoverCmdsCmd_t *pDiscoverCmd;
  uint8 *pBuf = pCmd->pData;

  pDiscoverCmd = (zclDiscoverCmdsCmd_t *)osal_mem_alloc( sizeof ( zclDiscoverCmdsCmd_t ) );
  if ( pDiscoverCmd != 0 )
  {
    pDiscoverCmd->startCmdID = *pBuf++;
    pDiscoverCmd->maxCmdID = *pBuf++;
  }
  Frama_C_dump_each();
  return ( (void *)pDiscoverCmd );
}

/*********************************************************************
 * @fn      zclParseInDiscCmdsRspCmd
 *
 * @brief   Parse the Discover Commands Response Command
 *
 *      NOTE: THIS FUNCTION ALLOCATES THE RETURN BUFFER, SO THE CALLING
 *            FUNCTION IS RESPONSIBLE TO FREE THE MEMORY.
 *
 * @param   pCmd - pointer to incoming data to parse
 *
 * @return  pointer to the parsed command structure
 */

static void *zclParseInDiscCmdsRspCmd( zclParseCmd_t *pCmd )
{
  zclDiscoverCmdsCmdRsp_t *pDiscoverRspCmd;
  uint8 *pBuf = pCmd->pData;
  uint8 numCmds = ((pCmd->dataLen)-1);  // length of command ID variable array

    // allocate memory for size of structure plus variable array
  pDiscoverRspCmd = (zclDiscoverCmdsCmdRsp_t *)osal_mem_alloc( sizeof ( zclDiscoverCmdsCmdRsp_t ) +
                    ( numCmds * sizeof(uint8) ) );
  if ( pDiscoverRspCmd != 0 )
  {
    uint8 i;
    pDiscoverRspCmd->discComplete = *pBuf++;
    pDiscoverRspCmd->numCmd = numCmds;

    for ( i = 0; i < numCmds; i++ )
    {
      pDiscoverRspCmd->pCmdID[i] = *pBuf++;
    }
  }
  Frama_C_dump_each();
  return ( (void *)pDiscoverRspCmd );
}

/*********************************************************************
 * @fn      zclParseInDiscAttrsExtRspCmd
 *
 * @brief   Parse the "Profile" Discovery Extended Attributes Response Commands
 *
 *      NOTE: THIS FUNCTION ALLOCATES THE RETURN BUFFER, SO THE CALLING
 *            FUNCTION IS RESPONSIBLE TO FREE THE MEMORY.
 *
 * @param   pCmd - pointer to incoming data to parse
 *
 * @return  pointer to the parsed command structure
 */

static void *zclParseInDiscAttrsExtRspCmd( zclParseCmd_t *pCmd )
{
  zclDiscoverAttrsExtRsp_t *pDiscoverRspCmd;
  uint8 i;
  uint8 *pBuf = pCmd->pData;
  uint8 numAttrs = ((pCmd->dataLen)-1) / ( 2 + 1 + 1 ); // Attr ID + Data Type + Access Control

  pDiscoverRspCmd = (zclDiscoverAttrsExtRsp_t *)osal_mem_alloc( sizeof ( zclDiscoverAttrsExtRsp_t ) +
                    ( numAttrs * sizeof(zclExtAttrInfo_t) ) );

  if ( pDiscoverRspCmd != 0 )
  {
    pDiscoverRspCmd->discComplete = *pBuf++;
    pDiscoverRspCmd->numAttr = numAttrs;

    for ( i = 0; i < numAttrs; i++ )
    {
      pDiscoverRspCmd->aExtAttrInfo[i].attrID = ((uint16)(((pBuf[0]) & 0x00FF) + (((pBuf[1]) & 0x00FF) << 8)));
      pBuf += 2;
      pDiscoverRspCmd->aExtAttrInfo[i].attrDataType = *pBuf++;
      pDiscoverRspCmd->aExtAttrInfo[i].attrAccessControl = *pBuf++;
    }
  }
  Frama_C_dump_each();
  return ( (void *)pDiscoverRspCmd );
}



/*********************************************************************
 * @fn      zclProcessInReadCmd
 *
 * @brief   Process the "Profile" Read Command
 *
 * @param   pInMsg - incoming message to process
 *
 * @return  TRUE if command processed. FALSE, otherwise.
 */
static uint8 zclProcessInReadCmd( zclIncoming_t *pInMsg )
{
  uint8 data[] = {0,1,0,0,0};
  //@ taint data[0];
  afIncomingMSGPacket_t msg = {
    .endPoint = 0x06,
    .clusterId = 0x0000,
    .cmd.Data = &data,
    .cmd.DataLength = sizeof(data),
    .cmd.TransSeqNumber = 1,
  };
  pInMsg->hdr.commandID = 0x00;
  pInMsg->hdr.transSeqNum = 1;
  pInMsg->hdr.fc.type = 0;
  pInMsg->hdr.fc.manuSpecific = 0;
  pInMsg->hdr.fc.direction = 0;
  pInMsg->hdr.fc.disableDefaultRsp = 0;
  pInMsg->msg = &msg;
  zclReadCmd_t testCmd = {
    .numAttr = 1,
  };
  pInMsg->attrCmd = &testCmd;
  /////////////////////////////////////////////////////////////////
    
  zclReadCmd_t *readCmd;
  zclReadRspCmd_t *readRspCmd;
  zclAttrRec_t attrRec;
  uint16 len;
  uint8 i;
  uint8 attrFound;

  readCmd = (zclReadCmd_t *)pInMsg->attrCmd;

  // calculate the length of the response status record
  len = sizeof( zclReadRspCmd_t ) + (readCmd->numAttr * sizeof( zclReadRspStatus_t ));

  readRspCmd = osal_mem_alloc( len );
  if ( readRspCmd == 0 )
  {
    return 0; // EMBEDDED RETURN
  }
  Frama_C_dump_each();
  readRspCmd->numAttr = readCmd->numAttr;
  for ( i = 0; i < readCmd->numAttr; i++ )
  {
    zclReadRspStatus_t *statusRec = &(readRspCmd->attrList[i]);

    statusRec->attrID = readCmd->attrID[i];
    
    attrFound = zclFindAttrRec( pInMsg->msg->endPoint, pInMsg->msg->clusterId, readCmd->attrID[i], &attrRec );
    
    //Validate the attribute is found and the access control
    if ( ( attrFound == 1 ) && 
         (  (attrRec.attr.accessControl & 0x40) || 
            ((((&attrRec . attr . accessControl)[((0x07) / 8)] & (1 << ((0x07) % 8))) ? 1 : 0) == pInMsg->hdr.fc.direction ) ) )
    {
      if ( ( (attrRec . attr . accessControl) & 0x01 ) )
      {
        statusRec->status = zclAuthorizeRead( pInMsg->msg->endPoint,
                                              &(pInMsg->msg->srcAddr), &attrRec );
        if ( statusRec->status == 0x00 )
        {
          statusRec->data = attrRec.attr.dataPtr;
          statusRec->dataType = attrRec.attr.dataType;
        }
      }
      else
      {
        statusRec->status = 0x8f;
      }
    }
    else
    {
      statusRec->status = 0x86;
    }
  }

  // Build and send Read Response command
  zcl_SendReadRsp( pInMsg->msg->endPoint, &(pInMsg->msg->srcAddr), pInMsg->msg->clusterId,
                   readRspCmd, !pInMsg->hdr.fc.direction,
                   1, pInMsg->hdr.transSeqNum );
  osal_mem_free( readRspCmd );
  Frama_C_dump_each();
  return 1;
}



/*********************************************************************
 * @fn      processInWriteCmd
 *
 * @brief   Process the "Profile" Write and Write No Response Commands
 *
 * @param   pInMsg - incoming message to process
 *
 * @return  TRUE if command processed. FALSE, otherwise.
 */
static uint8 zclProcessInWriteCmd( zclIncoming_t *pInMsg )
{
  uint8 data[] = {0,1,2,0,0,32,0x34,0x12};
  //@ taint data[0];
  afIncomingMSGPacket_t msg = {
    .endPoint = 0x08,
    .clusterId = 0x0000,
    .cmd.Data = &data,
    .cmd.DataLength = sizeof(data),
    .cmd.TransSeqNumber = 1,
  };
  pInMsg->hdr.commandID = data[2];
  pInMsg->hdr.transSeqNum = 1;
  pInMsg->hdr.fc.type = data[0];
  pInMsg->hdr.fc.manuSpecific = data[0];
  pInMsg->hdr.fc.direction = data[0];
  pInMsg->hdr.fc.disableDefaultRsp = data[0];
  pInMsg->msg = &msg;
  zclWriteCmd_t testCmd = {.numAttr = 1,};
  zclWriteRec_t testAttr;
  testAttr.attrID = (data[3] & 0x00FF) + ((data[4] & 0x00FF) << 8),
  testAttr.dataType = data[5],
  testAttr.attrData = (data[6] & 0x00FF) + ((data[7] & 0x00FF) << 8),
  pInMsg->attrCmd = &testCmd;
  /////////////////////////////////////////////////////////////////  
  zclWriteCmd_t *writeCmd;
  zclWriteRspCmd_t *writeRspCmd;
  uint8 sendRsp = 0;
  uint8 j = 0;
  uint8 i;

  writeCmd = (zclWriteCmd_t *)pInMsg->attrCmd;
  if ( pInMsg->hdr.commandID == 0x02 )
  {
    // We need to send a response back - allocate space for it
    writeRspCmd = (zclWriteRspCmd_t *)osal_mem_alloc( sizeof( zclWriteRspCmd_t )
            + sizeof( zclWriteRspStatus_t ) * writeCmd->numAttr );
    if ( writeRspCmd == 0 )
    {
      Frama_C_dump_each();
      return 0; // EMBEDDED RETURN
    }

    sendRsp = 1;
  }

  for ( i = 0; i < writeCmd->numAttr; i++ )
  {
    zclAttrRec_t attrRec;
    zclWriteRec_t *statusRec = &testAttr;
    //zclWriteRec_t *statusRec = &(writeCmd->attrList[i]);

    if ( zclFindAttrRec( pInMsg->msg->endPoint, pInMsg->msg->clusterId,
                         statusRec->attrID, &attrRec ) )
    {
      if ( (((&attrRec . attr . accessControl)[((0x07) / 8)] & (1 << ((0x07) % 8))) ? 1 : 0) != pInMsg->hdr.fc.direction )
      {
        Frama_C_dump_each();
        writeRspCmd->attrList[j].status = 0x86;
        writeRspCmd->attrList[j++].attrID = statusRec->attrID;
        break;
      }
	  
      if ( statusRec->dataType == attrRec.attr.dataType )
      {
        uint8 status;

        // Write the new attribute value
        if ( attrRec.attr.dataPtr != 0 )
        {
          //Handle special case for Identify
          if((pInMsg->msg->clusterId == 0x0003) && (statusRec->attrID == 0x0000))
          {
            uint16 identifyTime; 
                  
            osal_memcpy((uint8*)&identifyTime,statusRec->attrData,sizeof(uint16));
                        
            bdb_ZclIdentifyCmdInd(identifyTime, pInMsg->msg->endPoint);
            
            status = 0x00;
          }          
          else
          {                
            status = zclWriteAttrData( pInMsg->msg->endPoint, &(pInMsg->msg->srcAddr),
                                       &attrRec, statusRec );
          }
        }
        else // Use CB
        {
          status = zclWriteAttrDataUsingCB( pInMsg->msg->endPoint, &(pInMsg->msg->srcAddr),
                                            &attrRec, statusRec->attrData );
        }

        // If successful, a write attribute status record shall NOT be generated
        if ( sendRsp && status != 0x00 )
        {
          // Attribute is read only - move on to the next write attribute record
          writeRspCmd->attrList[j].status = status;
          writeRspCmd->attrList[j++].attrID = statusRec->attrID;
        }
      }
      else
      {
        // Attribute data type is incorrect - move on to the next write attribute record
        if ( sendRsp )
        {
          writeRspCmd->attrList[j].status = 0x8d;
          writeRspCmd->attrList[j++].attrID = statusRec->attrID;
        }
      }
    }
    else
    {
      // Attribute is not supported - move on to the next write attribute record
      if ( sendRsp )
      {
        writeRspCmd->attrList[j].status = 0x86;
        writeRspCmd->attrList[j++].attrID = statusRec->attrID;
      }
    }
    Frama_C_dump_each();
  } // for loop
  
  if ( sendRsp )
  {
    writeRspCmd->numAttr = j;
    if ( writeRspCmd->numAttr == 0 )
    {
      // Since all records were written successful, include a single status record
      // in the resonse command with the status field set to SUCCESS and the
      // attribute ID field omitted.
      writeRspCmd->attrList[0].status = 0x00;
      writeRspCmd->numAttr = 1;
    }

    zcl_SendWriteRsp( pInMsg->msg->endPoint, &(pInMsg->msg->srcAddr),
                      pInMsg->msg->clusterId, writeRspCmd, !pInMsg->hdr.fc.direction,
                      1, pInMsg->hdr.transSeqNum );
    osal_mem_free( writeRspCmd );
  }
  Frama_C_dump_each();
  return 1;
}

/*********************************************************************
 * @fn      zclRevertWriteUndividedCmd
 *
 * @brief   Revert the "Profile" Write Undevided Command
 *
 * @param   pInMsg - incoming message to process
 * @param   curWriteRec - old data
 * @param   numAttr - number of attributes to be reverted
 *
 * @return  none
 */
static void zclRevertWriteUndividedCmd( zclIncoming_t *pInMsg,
                                    zclWriteRec_t *curWriteRec, uint16 numAttr )
{
  uint8 i;

  for ( i = 0; i < numAttr; i++ )
  {
    zclAttrRec_t attrRec;
    zclWriteRec_t *statusRec = &(curWriteRec[i]);

    if ( !zclFindAttrRec( pInMsg->msg->endPoint, pInMsg->msg->clusterId,
                          statusRec->attrID, &attrRec ) )
    {
      break; // should never happen
    }

    if ( attrRec.attr.dataPtr != 0 )
    {
      // Just copy the old data back - no need to validate the data
      uint16 dataLen = zclGetAttrDataLength( attrRec.attr.dataType, statusRec->attrData );
      osal_memcpy( attrRec.attr.dataPtr, statusRec->attrData, dataLen );
    }
    else // Use CB
    {
      // Write the old data back
      zclWriteAttrDataUsingCB( pInMsg->msg->endPoint, &(pInMsg->msg->srcAddr),
                               &attrRec, statusRec->attrData );
    }
  } // for loop
  Frama_C_dump_each();
}

/*********************************************************************
 * @fn      zclProcessInWriteUndividedCmd
 *
 * @brief   Process the "Profile" Write Undivided Command
 *
 * @param   pInMsg - incoming message to process
 *
 * @return  TRUE if command processed. FALSE, otherwise.
 */
static uint8 zclProcessInWriteUndividedCmd( zclIncoming_t *pInMsg )
{
  uint8 data[] = {0,1,2,0,0,32,0x34,0x12};
  //@ taint data[0];
  afIncomingMSGPacket_t msg = {
    .endPoint = 0x08,
    .clusterId = 0x0000,
    .cmd.Data = &data,
    .cmd.DataLength = sizeof(data),
    .cmd.TransSeqNumber = 1,
  };
  pInMsg->hdr.commandID = data[2];
  pInMsg->hdr.transSeqNum = 1;
  pInMsg->hdr.fc.type = data[0];
  pInMsg->hdr.fc.manuSpecific = data[0];
  pInMsg->hdr.fc.direction = data[0];
  pInMsg->hdr.fc.disableDefaultRsp = data[0];
  pInMsg->msg = &msg;
  zclWriteCmd_t testCmd = {.numAttr = 1,};
  zclWriteRec_t testAttr = {
    .attrID = (data[3] & 0x00FF) + ((data[4] & 0x00FF) << 8),
    .dataType = data[5],
    .attrData = (data[6] & 0x00FF) + ((data[7] & 0x00FF) << 8),
  };
  pInMsg->attrCmd = &testCmd;
  
  zclWriteRspCmd_t testRspCmd = {.numAttr = 1,};
  /////////////////////////////////////////////////////////////////
  
  zclWriteCmd_t *writeCmd;
  zclWriteRspCmd_t *writeRspCmd;
  zclAttrRec_t attrRec;
  uint16 dataLen;
  uint16 curLen = 0;
  uint8 j = 0;
  uint8 i;

  writeCmd = (zclWriteCmd_t *)pInMsg->attrCmd;

  // Allocate space for Write Response Command
  writeRspCmd = (zclWriteRspCmd_t *)osal_mem_alloc( sizeof( zclWriteRspCmd_t )
                   + sizeof( zclWriteRspStatus_t )* writeCmd->numAttr );
  writeRspCmd = &testRspCmd;
  if ( writeRspCmd == 0 )
  {
    return 0; // EMBEDDED RETURN
  }

  // If any attribute cannot be written, no attribute values are changed. Hence,
  // make sure all the attributes are supported and writable
  for ( i = 0; i < writeCmd->numAttr; i++ )
  {
    // zclWriteRec_t *statusRec = &(writeCmd->attrList[i]);
    zclWriteRec_t *statusRec = &testAttr;  // Manual inject
    if ( !zclFindAttrRec( pInMsg->msg->endPoint, pInMsg->msg->clusterId,
                          statusRec->attrID, &attrRec ) )
    {
      Frama_C_dump_each();
      // Attribute is not supported - stop here
      writeRspCmd->attrList[j].status = 0x86;
      writeRspCmd->attrList[j++].attrID = statusRec->attrID;
      break;
    }

    if ( statusRec->dataType != attrRec.attr.dataType )
    {
      // Attribute data type is incorrect - stope here
      writeRspCmd->attrList[j].status = 0x8d;
      writeRspCmd->attrList[j++].attrID = statusRec->attrID;
      break;
    }

    if ( !( (attrRec . attr . accessControl) & 0x02 ) )
    {
      // Attribute is not writable - stop here
      writeRspCmd->attrList[j].status = 0x88;
      writeRspCmd->attrList[j++].attrID = statusRec->attrID;
      break;
    }

    if ( ( (attrRec . attr . accessControl) & 0x20 ) )
    {
      // Not authorized to write - stop here
      writeRspCmd->attrList[j].status = 0x7E;
      writeRspCmd->attrList[j++].attrID = statusRec->attrID;
      break;
    }

    // Attribute Data length
    if ( attrRec.attr.dataPtr != 0 )
    {
      dataLen = zclGetAttrDataLength( attrRec.attr.dataType, attrRec.attr.dataPtr );
    }
    else // Use CB
    {
      dataLen = zclGetAttrDataLengthUsingCB( pInMsg->msg->endPoint, pInMsg->msg->clusterId,
                                             statusRec->attrID );
    }

    // add padding if needed
    if ( ( (dataLen) % 2 ) )
    {
      dataLen++;
    }

    curLen += dataLen;
    Frama_C_dump_each();
  } // for loop

  writeRspCmd->numAttr = j;
  if ( writeRspCmd->numAttr == 0 ) // All attributes can be written
  {
    uint8 *curDataPtr;
    zclWriteRec_t *curWriteRec;

    // calculate the length of the current data header
    uint8 hdrLen = j * sizeof( zclWriteRec_t );

    // Allocate space to keep a copy of the current data
    curWriteRec = (zclWriteRec_t *) osal_mem_alloc( hdrLen + curLen );
    if ( curWriteRec == 0 )
    {
      osal_mem_free(writeRspCmd );
      return 0; // EMBEDDED RETURN
    }

    curDataPtr = (uint8 *)((uint8 *)curWriteRec + hdrLen);

    // Write the new data over
    for ( i = 0; i < writeCmd->numAttr; i++ )
    {
      uint8 status;
      zclWriteRec_t *statusRec = &testAttr; //&(writeCmd->attrList[i]);
      zclWriteRec_t *curStatusRec = &testAttr; //&(curWriteRec[i]);

      if ( !zclFindAttrRec( pInMsg->msg->endPoint, pInMsg->msg->clusterId,
                            statusRec->attrID, &attrRec ) )
      {
        break; // should never happen
      }

      // Keep a copy of the current data before before writing the new data over
      curStatusRec->attrID = statusRec->attrID;
      curStatusRec->attrData = curDataPtr;

      if ( attrRec.attr.dataPtr != 0 )
      {
        // Read the current value
        zclReadAttrData( curDataPtr, &attrRec, &dataLen );

        // Write the new attribute value
        status = zclWriteAttrData( pInMsg->msg->endPoint, &(pInMsg->msg->srcAddr),
                                   &attrRec, statusRec );
      }
      else // Use CBs
      {
        // Read the current value
        zclReadAttrDataUsingCB( pInMsg->msg->endPoint, pInMsg->msg->clusterId,
                                statusRec->attrID, curDataPtr, &dataLen );
        // Write the new attribute value
        status = zclWriteAttrDataUsingCB( pInMsg->msg->endPoint, &(pInMsg->msg->srcAddr),
                                          &attrRec, statusRec->attrData );
      }

      // If successful, a write attribute status record shall NOT be generated
      if ( status != 0x00 )
      {
        Frama_C_dump_each();
        writeRspCmd->attrList[j].status = status;
        writeRspCmd->attrList[j++].attrID = statusRec->attrID;

        // Since this write failed, we need to revert all the pervious writes
        zclRevertWriteUndividedCmd( pInMsg, curWriteRec, i);
        break;
      }

      // add padding if needed
      if ( ( (dataLen) % 2 ) )
      {
        dataLen++;
      }

      curDataPtr += dataLen;
      Frama_C_dump_each();
    } // for loop

    writeRspCmd->numAttr = j;
    if ( writeRspCmd->numAttr  == 0 )
    {
      // Since all records were written successful, include a single status record
      // in the resonse command with the status field set to SUCCESS and the
      // attribute ID field omitted.
      writeRspCmd->attrList[0].status = 0x00;
      writeRspCmd->numAttr = 1;
    }

    osal_mem_free( curWriteRec );
  }

  zcl_SendWriteRsp( pInMsg->msg->endPoint, &(pInMsg->msg->srcAddr),
                    pInMsg->msg->clusterId, writeRspCmd, !pInMsg->hdr.fc.direction,
                    1, pInMsg->hdr.transSeqNum );
  osal_mem_free( writeRspCmd );
  Frama_C_dump_each();
  return 1;
}



/*********************************************************************
 * @fn      zclProcessInDiscAttrs
 *
 * @brief   Process the "Profile" Discover Attributes Commands
 *
 * @param   pInMsg - incoming message to process
 *
 * @return  TRUE if command processed. FALSE, otherwise.
 */
static uint8 zclProcessInDiscAttrs( zclIncoming_t *pInMsg )
{
  uint8 data[] = {0,1,12,0,0,5};
  //@ taint data[0];
  afIncomingMSGPacket_t msg = {
    .endPoint = 0x08,
    .clusterId = 0x0000,
    .cmd.Data = &data,
    .cmd.DataLength = sizeof(data),
    .cmd.TransSeqNumber = 1,
  };
  pInMsg->hdr.commandID = data[2];
  pInMsg->hdr.transSeqNum = 1;
  pInMsg->hdr.fc.type = data[0];
  pInMsg->hdr.fc.manuSpecific = data[0];
  pInMsg->hdr.fc.direction = data[0];
  pInMsg->hdr.fc.disableDefaultRsp = data[0];
  pInMsg->msg = &msg;
  
  zclDiscoverAttrsCmd_t testCmd = {
    .startAttr = (data[3] & 0x00FF) + ((data[4] & 0x00FF) << 8),
    .maxAttrIDs = data[5],
  };
  pInMsg->attrCmd = &testCmd;
  //////////////////////////////////////////////////////
  
  zclDiscoverAttrsCmd_t *pDiscoverCmd;
  zclAttrRec_t attrRec;
  uint16 attrID;
  uint8 numAttrs;
  uint8 i;

  pDiscoverCmd = (zclDiscoverAttrsCmd_t *)pInMsg->attrCmd;

  // Find out the number of attributes supported within the specified range
  for ( i = 0, attrID = pDiscoverCmd->startAttr; i < pDiscoverCmd->maxAttrIDs; i++, attrID++ )
  {
    // finds the next attribute on this endpoint/cluster after the range.
    // attributes must be in numerical order in the list.
    if ( !zclFindNextAttrRec( pInMsg->msg->endPoint, pInMsg->msg->clusterId, pInMsg->hdr.fc.direction, &attrID, &attrRec ) )
    {
      break;
    }
  }

  numAttrs = i;  // store range of attributes in buffer

    // Process message for either attributes or extended attributes
  if( pInMsg->hdr.commandID == 0x0c )
  {
    zclProcessInDiscAttrsCmd( pInMsg, pDiscoverCmd, numAttrs );
  }
  else if ( pInMsg->hdr.commandID == 0x15 )
  {
    zclProcessInDiscAttrsExtCmd( pInMsg, pDiscoverCmd, numAttrs );
  }
  Frama_C_dump_each();
  return 1;
}

/*********************************************************************
 * @fn      zclProcessInDiscAttrsCmd
 *
 * @brief   Process the Discover Attributes Command
 *
 * @param   pInMsg - incoming message to process
 *
 * @param   pDiscoverCmd - structure from requesting command
 *
 * @param   attrLenBuf - describes the amount of attributes to be processed
 *
 * @return  none
 */
static void zclProcessInDiscAttrsCmd( zclIncoming_t *pInMsg, zclDiscoverAttrsCmd_t *pDiscoverCmd, uint8 numAttrs )
{
  zclDiscoverAttrsRspCmd_t *pDiscoverRsp;
  uint8 discComplete = 1;
  zclAttrRec_t attrRec;
  uint16 attrID;
  uint8 i;

  // Allocate space for the response command
  pDiscoverRsp = (zclDiscoverAttrsRspCmd_t *)osal_mem_alloc( sizeof (zclDiscoverAttrsRspCmd_t)
                                                          + sizeof ( zclDiscoverAttrInfo_t ) * numAttrs );
  if ( pDiscoverRsp == 0 )
  {
    return; // EMBEDDED RETURN
  }

  if ( numAttrs != 0 )
  {
    for ( i = 0, attrID = pDiscoverCmd->startAttr; i < numAttrs; i++, attrID++ )
    {
      if ( !zclFindNextAttrRec( pInMsg->msg->endPoint, pInMsg->msg->clusterId, pInMsg->hdr.fc.direction, &attrID, &attrRec ) )
      {
        break; // should not happen, as numAttrs already calculated
      }

      pDiscoverRsp->attrList[i].attrID = attrRec.attr.attrId;
      pDiscoverRsp->attrList[i].dataType = attrRec.attr.dataType;
    }

    // Are there more attributes to be discovered?
    if ( zclFindNextAttrRec( pInMsg->msg->endPoint, pInMsg->msg->clusterId, pInMsg->hdr.fc.direction, &attrID, &attrRec ) )
    {
      discComplete = 0;
    }
  }

  pDiscoverRsp->discComplete = discComplete;
  pDiscoverRsp->numAttr = numAttrs;

  zcl_SendDiscoverAttrsRspCmd( pInMsg->msg->endPoint, &pInMsg->msg->srcAddr,
                               pInMsg->msg->clusterId, pDiscoverRsp, !(pInMsg->hdr.fc.direction),
                               1, pInMsg->hdr.transSeqNum );
  osal_mem_free( pDiscoverRsp );
  Frama_C_dump_each();
  return;
}

/*********************************************************************
 * @fn      zclProcessInDiscAttrsExtCmd
 *
 * @brief   Process the Discover Attributes Extended Command
 *
 * @param   pInMsg - incoming message to process
 *
 * @param   pDiscoverCmd - structure from requesting command
 *
 * @param   attrLenBuf - describes the amount of attributes to be processed
 *
 * @return  none
 */
static void zclProcessInDiscAttrsExtCmd( zclIncoming_t *pInMsg, zclDiscoverAttrsCmd_t *pDiscoverCmd, uint8 numAttrs )
{
  zclDiscoverAttrsExtRsp_t *pDiscoverExtRsp;
  uint8 discComplete = 1;
  zclAttrRec_t attrRec;
  uint16 attrID;
  uint8 i;

    // Allocate space for the response command
  pDiscoverExtRsp = (zclDiscoverAttrsExtRsp_t *)osal_mem_alloc( sizeof (zclDiscoverAttrsExtRsp_t)
                                                         + sizeof ( zclExtAttrInfo_t ) * numAttrs );
  if ( pDiscoverExtRsp == 0 )
  {
    return; // EMBEDDED RETURN
  }


  if ( numAttrs != 0 )
  {
    for ( i = 0, attrID = pDiscoverCmd->startAttr; i < numAttrs; i++, attrID++ )
    {
      if ( !zclFindNextAttrRec( pInMsg->msg->endPoint, pInMsg->msg->clusterId, pInMsg->hdr.fc.direction, &attrID, &attrRec ) )
      {
        break; // Should not happen, as numAttrs already calculated
      }

      pDiscoverExtRsp->aExtAttrInfo[i].attrID = attrRec.attr.attrId;
      pDiscoverExtRsp->aExtAttrInfo[i].attrDataType = attrRec.attr.dataType;
      pDiscoverExtRsp->aExtAttrInfo[i].attrAccessControl = attrRec.attr.accessControl & 0x07;
    }

    // Are there more attributes to be discovered?
    if ( zclFindNextAttrRec( pInMsg->msg->endPoint, pInMsg->msg->clusterId, pInMsg->hdr.fc.direction, &attrID, &attrRec ) )
    {
      discComplete = 0;
    }
  }

  pDiscoverExtRsp->discComplete = discComplete;
  pDiscoverExtRsp->numAttr = numAttrs;

  zcl_SendDiscoverAttrsExtRsp( pInMsg->msg->endPoint, &pInMsg->msg->srcAddr,
                               pInMsg->msg->clusterId, pDiscoverExtRsp, !(pInMsg->hdr.fc.direction),
                               1, pInMsg->hdr.transSeqNum );

  osal_mem_free( pDiscoverExtRsp );
  Frama_C_dump_each();
  return;
}

/*********************************************************************
 * @fn      zclProcessInDiscCmd
 *
 * @brief   Process the "Profile" Discover Command
 *
 * @param   pInMsg - incoming message to process
 *
 * @return  TRUE if command processed. FALSE, otherwise.
 */
static uint8 zclProcessInDiscCmd( zclIncoming_t *pInMsg )
{
  uint8 data[] = {0,1,17,0,5};
  //@ taint data[4];
  afIncomingMSGPacket_t msg = {
    .endPoint = 0x08,
    .clusterId = 0x0000,
    .cmd.Data = &data,
    .cmd.DataLength = sizeof(data),
    .cmd.TransSeqNumber = 1,
  };
  pInMsg->hdr.commandID = data[2];
  pInMsg->hdr.transSeqNum = 1;
  pInMsg->hdr.fc.type = data[0];
  pInMsg->hdr.fc.manuSpecific = data[0];
  pInMsg->hdr.fc.direction = data[0];
  pInMsg->hdr.fc.disableDefaultRsp = data[0];
  pInMsg->msg = &msg;
  
  zclDiscoverCmdsCmd_t testCmd = {
    .startCmdID = data[3],
    .maxCmdID = data[4],
  };
  pInMsg->attrCmd = &testCmd;
  ///////////////////////////////////////////////////////////////
  
  zclDiscoverCmdsCmd_t *pDiscoverCmd;
  zclDiscoverCmdsCmdRsp_t cmdRsp;
  ZStatus_t status;
  zclCommandRec_t cmdRec;
  uint8 cmdID;
  uint8 i;
  uint8 j;

  pDiscoverCmd = (zclDiscoverCmdsCmd_t *)pInMsg->attrCmd;

  // Find out the number of commands supported within the specified range
  for ( i = 0, cmdID = pDiscoverCmd->startCmdID; i < pDiscoverCmd->maxCmdID; i++, cmdID++ )
  {
    if ( !zclFindNextCmdRec( pInMsg->msg->endPoint, pInMsg->msg->clusterId, pInMsg->hdr.commandID, pInMsg->hdr.fc.direction, &cmdID, &cmdRec ) )
    {
      break;  // Command not supported
    }
  }

  // Allocate space for the response command
  cmdRsp.pCmdID = osal_mem_alloc( i ); // size of number of commands returned
  cmdRsp.pCmdID[0] = i; 

  if ( cmdRsp.pCmdID == 0 )
  {
    return 0; // EMBEDDED RETURN
  }

  if ( i != 0 )
  {
    for ( j = 0, cmdID = pDiscoverCmd->startCmdID; j < i; j++, cmdID++ )
    {
      if ( !zclFindNextCmdRec( pInMsg->msg->endPoint, pInMsg->msg->clusterId, pInMsg->hdr.commandID, pInMsg->hdr.fc.direction, &cmdID, &cmdRec ) )
      {
        break; // Attribute not supported
      }

      cmdRsp.pCmdID[j] = cmdRec.cmdID;
    }
  }

  // Are there more commands to be discovered?
  if ( zclFindNextCmdRec( pInMsg->msg->endPoint, pInMsg->msg->clusterId, pInMsg->hdr.commandID, pInMsg->hdr.fc.direction, &cmdID, &cmdRec ) )
  {
    cmdRsp.discComplete = 0;
  }
  else
  {
    cmdRsp.discComplete = 1;
  }

  // pass the command requested
  cmdRsp.cmdType = pInMsg->hdr.commandID;

  // store number of commands returned
  cmdRsp.numCmd = j;

  status = zcl_SendDiscoverCmdsRspCmd( pInMsg->msg->endPoint, &pInMsg->msg->srcAddr,
                                      pInMsg->msg->clusterId, &cmdRsp, !(pInMsg->hdr.fc.direction),
                                      1, pInMsg->hdr.transSeqNum );

  osal_mem_free( cmdRsp.pCmdID );

  if ( status == 0x00 )
  {
    Frama_C_dump_each();
    return 1;
  }
  else
  {
    Frama_C_dump_each();
    return 0;
  }
}




/*********************************************************************
*********************************************************************/
