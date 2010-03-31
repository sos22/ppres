module Config(rescheduleOnEveryAccess, useMemoryRecords,
              validateHistories) where

useMemoryRecords :: Bool
useMemoryRecords = False

rescheduleOnEveryAccess :: Bool
rescheduleOnEveryAccess = useMemoryRecords

validateHistories :: Bool
validateHistories = False
