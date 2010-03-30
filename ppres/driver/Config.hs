module Config(rescheduleOnEveryAccess, useMemoryRecords) where

useMemoryRecords :: Bool
useMemoryRecords = True

rescheduleOnEveryAccess :: Bool
rescheduleOnEveryAccess = useMemoryRecords