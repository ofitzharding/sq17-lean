import Sq17Lean.LocalRigidityResidualSupport
namespace Sq17.LocalRigidity.ResidualData
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
def mid000 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target000 : Fin 45 → ℚ := fun j => if j.val = 0 then 1 else 0
def mid001 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target001 : Fin 45 → ℚ := fun j => if j.val = 0 then -1 else 0
def mid002 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target002 : Fin 45 → ℚ := fun j => if j.val = 1 then 1 else 0
def mid003 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target003 : Fin 45 → ℚ := fun j => if j.val = 1 then -1 else 0
def mid004 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target004 : Fin 45 → ℚ := fun j => if j.val = 2 then 1 else 0
def mid005 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target005 : Fin 45 → ℚ := fun j => if j.val = 2 then -1 else 0
def mid006 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target006 : Fin 45 → ℚ := fun j => if j.val = 3 then 1 else 0
def mid007 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target007 : Fin 45 → ℚ := fun j => if j.val = 3 then -1 else 0
def mid008 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target008 : Fin 45 → ℚ := fun j => if j.val = 4 then 1 else 0
def mid009 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target009 : Fin 45 → ℚ := fun j => if j.val = 4 then -1 else 0
def mid010 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target010 : Fin 45 → ℚ := fun j => if j.val = 5 then 1 else 0
def mid011 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target011 : Fin 45 → ℚ := fun j => if j.val = 5 then -1 else 0
def mid012 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target012 : Fin 45 → ℚ := fun j => if j.val = 6 then 1 else 0
def mid013 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target013 : Fin 45 → ℚ := fun j => if j.val = 6 then -1 else 0
def mid014 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target014 : Fin 45 → ℚ := fun j => if j.val = 7 then 1 else 0
def mid015 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target015 : Fin 45 → ℚ := fun j => if j.val = 7 then -1 else 0
def mid016 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target016 : Fin 45 → ℚ := fun j => if j.val = 8 then 1 else 0
def mid017 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target017 : Fin 45 → ℚ := fun j => if j.val = 8 then -1 else 0
def mid018 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target018 : Fin 45 → ℚ := fun j => if j.val = 9 then 1 else 0
def mid019 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target019 : Fin 45 → ℚ := fun j => if j.val = 9 then -1 else 0
def mid020 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target020 : Fin 45 → ℚ := fun j => if j.val = 10 then 1 else 0
def mid021 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target021 : Fin 45 → ℚ := fun j => if j.val = 10 then -1 else 0
def mid022 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target022 : Fin 45 → ℚ := fun j => if j.val = 11 then 1 else 0
def mid023 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target023 : Fin 45 → ℚ := fun j => if j.val = 11 then -1 else 0
def mid024 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target024 : Fin 45 → ℚ := fun j => if j.val = 12 then 1 else 0
def mid025 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target025 : Fin 45 → ℚ := fun j => if j.val = 12 then -1 else 0
def mid026 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target026 : Fin 45 → ℚ := fun j => if j.val = 13 then 1 else 0
def mid027 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target027 : Fin 45 → ℚ := fun j => if j.val = 13 then -1 else 0
def mid028 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target028 : Fin 45 → ℚ := fun j => if j.val = 14 then 1 else 0
def mid029 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target029 : Fin 45 → ℚ := fun j => if j.val = 14 then -1 else 0
def mid030 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target030 : Fin 45 → ℚ := fun j => if j.val = 15 then 1 else 0
def mid031 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target031 : Fin 45 → ℚ := fun j => if j.val = 15 then -1 else 0
def mid032 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target032 : Fin 45 → ℚ := fun j => if j.val = 16 then 1 else 0
def mid033 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target033 : Fin 45 → ℚ := fun j => if j.val = 16 then -1 else 0
def mid034 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target034 : Fin 45 → ℚ := fun j => if j.val = 17 then 1 else 0
def mid035 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target035 : Fin 45 → ℚ := fun j => if j.val = 17 then -1 else 0
def mid036 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target036 : Fin 45 → ℚ := fun j => if j.val = 18 then 1 else 0
def mid037 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target037 : Fin 45 → ℚ := fun j => if j.val = 18 then -1 else 0
def mid038 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target038 : Fin 45 → ℚ := fun j => if j.val = 19 then 1 else 0
def mid039 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target039 : Fin 45 → ℚ := fun j => if j.val = 19 then -1 else 0
def mid040 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target040 : Fin 45 → ℚ := fun j => if j.val = 20 then 1 else 0
def mid041 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target041 : Fin 45 → ℚ := fun j => if j.val = 20 then -1 else 0
def mid042 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target042 : Fin 45 → ℚ := fun j => if j.val = 21 then 1 else 0
def mid043 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target043 : Fin 45 → ℚ := fun j => if j.val = 21 then -1 else 0
def mid044 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target044 : Fin 45 → ℚ := fun j => if j.val = 22 then 1 else 0
def mid045 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target045 : Fin 45 → ℚ := fun j => if j.val = 22 then -1 else 0
def mid046 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target046 : Fin 45 → ℚ := fun j => if j.val = 23 then 1 else 0
def mid047 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target047 : Fin 45 → ℚ := fun j => if j.val = 23 then -1 else 0
def mid048 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target048 : Fin 45 → ℚ := fun j => if j.val = 24 then 1 else 0
def mid049 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target049 : Fin 45 → ℚ := fun j => if j.val = 24 then -1 else 0
def mid050 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target050 : Fin 45 → ℚ := fun j => if j.val = 25 then 1 else 0
def mid051 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target051 : Fin 45 → ℚ := fun j => if j.val = 25 then -1 else 0
def mid052 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target052 : Fin 45 → ℚ := fun j => if j.val = 26 then 1 else 0
def mid053 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target053 : Fin 45 → ℚ := fun j => if j.val = 26 then -1 else 0
def mid054 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target054 : Fin 45 → ℚ := fun j => if j.val = 27 then 1 else 0
def mid055 : Fin 3 → ℚ := ![(1/8),(311/7500),(5/128)]
def target055 : Fin 45 → ℚ := fun j => if j.val = 27 then -1 else 0
def mid056 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/128)]
def target056 : Fin 45 → ℚ := fun j => if j.val = 27 then -1 else 0
def mid057 : Fin 3 → ℚ := ![(1/8),(311/7500),(-7/128)]
def target057 : Fin 45 → ℚ := fun j => if j.val = 27 then -1 else 0
def mid058 : Fin 3 → ℚ := ![(1/8),(311/7500),(-13/128)]
def target058 : Fin 45 → ℚ := fun j => if j.val = 27 then -1 else 0
def mid059 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target059 : Fin 45 → ℚ := fun j => if j.val = 28 then 1 else 0
def mid060 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target060 : Fin 45 → ℚ := fun j => if j.val = 28 then -1 else 0
def mid061 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target061 : Fin 45 → ℚ := fun j => if j.val = 29 then 1 else 0
def mid062 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target062 : Fin 45 → ℚ := fun j => if j.val = 29 then -1 else 0
def mid063 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target063 : Fin 45 → ℚ := fun j => if j.val = 30 then 1 else 0
def mid064 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target064 : Fin 45 → ℚ := fun j => if j.val = 30 then -1 else 0
def mid065 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target065 : Fin 45 → ℚ := fun j => if j.val = 31 then 1 else 0
def mid066 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target066 : Fin 45 → ℚ := fun j => if j.val = 31 then -1 else 0
def mid067 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target067 : Fin 45 → ℚ := fun j => if j.val = 32 then 1 else 0
def mid068 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target068 : Fin 45 → ℚ := fun j => if j.val = 32 then -1 else 0
def mid069 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target069 : Fin 45 → ℚ := fun j => if j.val = 33 then 1 else 0
def mid070 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target070 : Fin 45 → ℚ := fun j => if j.val = 33 then -1 else 0
def mid071 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target071 : Fin 45 → ℚ := fun j => if j.val = 34 then 1 else 0
def mid072 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target072 : Fin 45 → ℚ := fun j => if j.val = 34 then -1 else 0
def mid073 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target073 : Fin 45 → ℚ := fun j => if j.val = 35 then 1 else 0
def mid074 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target074 : Fin 45 → ℚ := fun j => if j.val = 35 then -1 else 0
def mid075 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target075 : Fin 45 → ℚ := fun j => if j.val = 36 then 1 else 0
def mid076 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target076 : Fin 45 → ℚ := fun j => if j.val = 36 then -1 else 0
def mid077 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target077 : Fin 45 → ℚ := fun j => if j.val = 37 then 1 else 0
def mid078 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target078 : Fin 45 → ℚ := fun j => if j.val = 37 then -1 else 0
def mid079 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target079 : Fin 45 → ℚ := fun j => if j.val = 38 then 1 else 0
def mid080 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target080 : Fin 45 → ℚ := fun j => if j.val = 38 then -1 else 0
def mid081 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target081 : Fin 45 → ℚ := fun j => if j.val = 39 then 1 else 0
def mid082 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target082 : Fin 45 → ℚ := fun j => if j.val = 39 then -1 else 0
def mid083 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target083 : Fin 45 → ℚ := fun j => if j.val = 40 then 1 else 0
def mid084 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target084 : Fin 45 → ℚ := fun j => if j.val = 40 then -1 else 0
def mid085 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target085 : Fin 45 → ℚ := fun j => if j.val = 41 then 1 else 0
def mid086 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target086 : Fin 45 → ℚ := fun j => if j.val = 41 then -1 else 0
def mid087 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target087 : Fin 45 → ℚ := fun j => if j.val = 42 then 1 else 0
def mid088 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target088 : Fin 45 → ℚ := fun j => if j.val = 42 then -1 else 0
def mid089 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target089 : Fin 45 → ℚ := fun j => if j.val = 43 then 1 else 0
def mid090 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target090 : Fin 45 → ℚ := fun j => if j.val = 43 then -1 else 0
def mid091 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target091 : Fin 45 → ℚ := fun j => if j.val = 44 then 1 else 0
def mid092 : Fin 3 → ℚ := ![(1/8),(311/7500),(-1/32)]
def target092 : Fin 45 → ℚ := fun j => if j.val = 44 then -1 else 0
def mid : Fin 93 → Fin 3 → ℚ := ![mid000,mid001,mid002,mid003,mid004,mid005,mid006,mid007,mid008,mid009,mid010,mid011,mid012,mid013,mid014,mid015,mid016,mid017,mid018,mid019,mid020,mid021,mid022,mid023,mid024,mid025,mid026,mid027,mid028,mid029,mid030,mid031,mid032,mid033,mid034,mid035,mid036,mid037,mid038,mid039,mid040,mid041,mid042,mid043,mid044,mid045,mid046,mid047,mid048,mid049,mid050,mid051,mid052,mid053,mid054,mid055,mid056,mid057,mid058,mid059,mid060,mid061,mid062,mid063,mid064,mid065,mid066,mid067,mid068,mid069,mid070,mid071,mid072,mid073,mid074,mid075,mid076,mid077,mid078,mid079,mid080,mid081,mid082,mid083,mid084,mid085,mid086,mid087,mid088,mid089,mid090,mid091,mid092]
def target : Fin 93 → Fin 45 → ℚ := ![target000,target001,target002,target003,target004,target005,target006,target007,target008,target009,target010,target011,target012,target013,target014,target015,target016,target017,target018,target019,target020,target021,target022,target023,target024,target025,target026,target027,target028,target029,target030,target031,target032,target033,target034,target035,target036,target037,target038,target039,target040,target041,target042,target043,target044,target045,target046,target047,target048,target049,target050,target051,target052,target053,target054,target055,target056,target057,target058,target059,target060,target061,target062,target063,target064,target065,target066,target067,target068,target069,target070,target071,target072,target073,target074,target075,target076,target077,target078,target079,target080,target081,target082,target083,target084,target085,target086,target087,target088,target089,target090,target091,target092]
def directionCol : Fin 90 → Fin 45 := ![0,0,1,1,2,2,3,3,4,4,5,5,6,6,7,7,8,8,9,9,10,10,11,11,12,12,13,13,14,14,15,15,16,16,17,17,18,18,19,19,20,20,21,21,22,22,23,23,24,24,25,25,26,26,27,27,28,28,29,29,30,30,31,31,32,32,33,33,34,34,35,35,36,36,37,37,38,38,39,39,40,40,41,41,42,42,43,43,44,44]
def directionSign : Fin 90 → ℚ := ![1,-1,1,-1,1,-1,1,-1,1,-1,1,-1,1,-1,1,-1,1,-1,1,-1,1,-1,1,-1,1,-1,1,-1,1,-1,1,-1,1,-1,1,-1,1,-1,1,-1,1,-1,1,-1,1,-1,1,-1,1,-1,1,-1,1,-1,1,-1,1,-1,1,-1,1,-1,1,-1,1,-1,1,-1,1,-1,1,-1,1,-1,1,-1,1,-1,1,-1,1,-1,1,-1,1,-1,1,-1,1,-1]
def positiveDirection : Fin 45 → Fin 90 := ![0,2,4,6,8,10,12,14,16,18,20,22,24,26,28,30,32,34,36,38,40,42,44,46,48,50,52,54,56,58,60,62,64,66,68,70,72,74,76,78,80,82,84,86,88]
def negativeDirection : Fin 45 → Fin 90 := ![1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39,41,43,45,47,49,51,53,55,57,59,61,63,65,67,69,71,73,75,77,79,81,83,85,87,89]
def signedIndex (j : Fin 45) (b : Bool) : Fin 90 := if b then positiveDirection j else negativeDirection j
theorem signedIndex_correct : ∀ j b, directionCol (signedIndex j b) = j ∧ directionSign (signedIndex j b) = (if b then 1 else -1) := by decide +kernel
theorem target_by_owner : ∀ i j, target i j = (if j = directionCol (WeightCoverData.owner i) then directionSign (WeightCoverData.owner i) else 0) := by decide +kernel
theorem mid_correct : ∀ i k, mid i k = (WeightCoverData.lower i k+WeightCoverData.upper i k)/2 := by decide +kernel

end Sq17.LocalRigidity.ResidualData
#print axioms Sq17.LocalRigidity.ResidualData.target_by_owner
