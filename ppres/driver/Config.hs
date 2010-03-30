module Config(rescheduleOnEveryAccess, useMemoryRecords) where

useMemoryRecords :: Bool
useMemoryRecords = False

rescheduleOnEveryAccess :: Bool
rescheduleOnEveryAccess = useMemoryRecords