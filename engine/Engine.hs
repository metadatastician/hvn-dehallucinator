-- SPDX-License-Identifier: MPL-2.0
-- The Harvard Dehallucinator state engine.
--
-- THE GUARANTEE: `completed` and `status` are only ever DERIVED from
-- engine/verify_register.sh. No caller can assert progress. There is no code
-- path from a command-line argument to the string "COMPLETE".
--
-- The original engine took `remaining` as a parameter, which put the progress
-- number back inside the agent's writable space -- the exact Von Neumann
-- collapse this project exists to prevent. That command has been removed.
--
-- The same collapse came back through the directory: `update <targetdir>`
-- measured whatever directory the caller named, so measuring an empty one
-- wrote COMPLETE while the real target was untouched (found 2026-11-09). The
-- target is now BOUND at the baseline: `init` and `init-from` record its
-- canonical path in the state file, and `update` and `verify` take no target
-- and measure only the bound one. The caller chooses what to work on once,
-- when the baseline is set, and never again.
module Main where

import Control.Exception (SomeException, try)
import Control.Monad (when)
import Data.Char (isControl, isDigit, isSpace)
import System.Directory
    (canonicalizePath, doesDirectoryExist, doesFileExist, getCurrentDirectory, renameFile)
import System.Environment (getArgs, lookupEnv)
import System.Exit (ExitCode (..), exitWith)
import System.FilePath ((</>), takeDirectory)
import System.IO (hPutStrLn, stderr)
import System.Process (readProcessWithExitCode)
import Text.Read (readMaybe)

-- ---------------------------------------------------------------- state ----

data State = State
    { totalItems :: Int
    , completed  :: Int
    , attempts   :: Int
    , status     :: String
    , target     :: FilePath   -- canonical; the only directory ever measured
    } deriving (Show)

statusRunning, statusComplete, statusStop :: String
statusRunning  = "RUNNING"
statusComplete = "COMPLETE"
statusStop     = "EMERGENCY_STOP"

-- How many attempts beyond totalItems before the breaker trips.
attemptSlack :: Int
attemptSlack = 5

-- The largest baseline accepted. It keeps totalItems + attemptSlack, and every
-- attempt count the breaker allows, far inside Int: before this bound,
-- `init 9223372036854775807` overflowed the breaker's sum and tripped on the
-- first attempt.
maxTotal :: Int
maxTotal = 1000000000000

-- A count is a natural number written in decimal digits and nothing else.
-- `read` alone accepted "-2", and a negative count then wrote completed > total.
natural :: String -> Maybe Int
natural s
    | not (null s), all isDigit s, length s <= 13 = readMaybe s
    | otherwise = Nothing

trim :: String -> String
trim = f . f where f = reverse . dropWhile isSpace

-- ----------------------------------------------------------- locating ------
-- Never cwd-relative. The original hardcoded "../state/state.txt", so the
-- engine only worked when invoked from engine/.

isRoot :: FilePath -> IO Bool
isRoot d = do
    v <- doesFileExist (d </> "engine" </> "verify_register.sh")
    s <- doesDirectoryExist (d </> "state")
    return (v && s)

findRoot :: IO (Either String FilePath)
findRoot = do
    override <- lookupEnv "HARVARD_ROOT"
    case override of
        Just p -> do
            ok <- isRoot p
            return $ if ok
                then Right p
                else Left ("HARVARD_ROOT is not a harvard-dehallucinator checkout: " ++ p)
        Nothing -> getCurrentDirectory >>= climb
  where
    climb d = do
        ok <- isRoot d
        if ok
            then return (Right d)
            else let up = takeDirectory d
                 in if up == d
                        then return (Left "could not locate the repo root: looked for \
                                          \engine/verify_register.sh and state/ from the \
                                          \working directory upward. Set HARVARD_ROOT.")
                        else climb up

stateFileOf, verifierOf :: FilePath -> FilePath
stateFileOf root = root </> "state" </> "state.txt"
verifierOf  root = root </> "engine" </> "verify_register.sh"

-- ------------------------------------------------------------ parsing ------
-- Total. The original used bare `read` and `error "Corrupted State File"`,
-- so any malformed field crashed the one component meant to be durable.

-- A state file is five lines: totalItems, completed, attempts, status, target.
-- Every field is checked, and so are the relations the engine itself keeps
-- (completed <= totalItems <= maxTotal, attempts <= totalItems + attemptSlack + 1),
-- so a hand-edited or truncated file is refused rather than acted on.
parseState :: String -> Either String State
parseState raw = case lines raw of
    [t, c, a, s, p] -> do
        st <- State <$> nat "totalItems" t
                    <*> nat "completed"  c
                    <*> nat "attempts"   a
                    <*> stat s
                    <*> path p
        check st
    ls -> Left ("state file malformed: expected 5 lines (total, completed, attempts, \
                \status, target), found " ++ show (length ls)
                ++ ". A 4-line file predates the bound target: set the baseline again \
                   \with `init-from <targetdir>`.")
  where
    nat lbl v = maybe (Left (lbl ++ ": not a natural number: " ++ show v)) Right
                      (natural (trim v))
    stat v
        | trim v `elem` [statusRunning, statusComplete, statusStop] = Right (trim v)
        | otherwise = Left ("status: not one of RUNNING, COMPLETE, EMERGENCY_STOP: " ++ show v)
    path v
        | badTarget v = Left ("target: contains a control character: " ++ show v)
        | take 1 v == "/" = Right v
        | otherwise = Left ("target: not an absolute path: " ++ show v)
    check st
        | totalItems st > maxTotal =
            Left ("totalItems: above the bound " ++ show maxTotal)
        | completed st > totalItems st =
            Left "completed: greater than totalItems"
        | attempts st > totalItems st + attemptSlack + 1 =
            Left "attempts: beyond what the circuit breaker allows"
        | otherwise = Right st

readState :: FilePath -> IO (Either String State)
readState root = do
    let f = stateFileOf root
    ok <- doesFileExist f
    if not ok
        then return (Left ("no state file at " ++ f ++ " - run `init` or `init-from` first"))
        else do
            raw <- readFile f
            length raw `seq` return (parseState raw)  -- force before we rewrite

-- Atomic. The layout is positional, so no field may contain a newline: status
-- is one of three constants, and a target with a newline is refused at
-- binding ('bindTarget').
writeState :: FilePath -> State -> IO ()
writeState root s = do
    let f     = stateFileOf root
        tmp   = f ++ ".tmp"
    writeFile tmp (unlines [ show (totalItems s), show (completed s)
                           , show (attempts s), status s, target s ])
    renameFile tmp f

-- The directory a baseline binds: it must exist, and is stored canonical, so
-- the state names exactly one directory however it was spelled.
bindTarget :: FilePath -> IO (Either String FilePath)
bindTarget dir = do
    ok <- doesDirectoryExist dir
    if not ok then return (Left ("target directory does not exist: " ++ dir)) else do
        p <- canonicalizePath dir
        return $ if badTarget p
            then Left ("target path contains a control character: " ++ show p)
            else Right p

-- A target is one line of the positional state file, and the engine never
-- writes one with a control character in it: binding refuses such a path, and
-- parsing refuses a stored one (a CRLF-edited file leaves `\r` on the line).
badTarget :: FilePath -> Bool
badTarget = any isControl

-- ----------------------------------------------------------- verifier ------
-- The sole source of truth about progress.

runVerifier :: FilePath -> FilePath -> IO (Either String Int)
runVerifier root target = do
    okT <- doesDirectoryExist target
    okV <- doesFileExist (verifierOf root)
    if not okT then return (Left ("target directory does not exist: " ++ target))
    else if not okV then return (Left ("verifier missing: " ++ verifierOf root))
    else do
        r <- try (readProcessWithExitCode "bash" [verifierOf root, target] "")
        return $ case r of
            Left e -> Left ("verifier failed to run: " ++ show (e :: SomeException))
            Right (ExitSuccess, out, _) ->
                maybe (Left ("verifier did not print a natural number: " ++ show out))
                      Right (natural (trim out))
            Right (code, _, err) ->
                Left ("verifier exited " ++ show code ++ ": " ++ trim err)

-- ------------------------------------------------------------ witness ------
-- When the engine regresses or refuses, it cites the blind-spot witness rather
-- than a bare verdict. The recorded state alone does not identify what
-- remains: a reading "as recorded" and a reading "as measured" both fit it and
-- disagree on COMPLETE (verification/proofs/agda/Fibre.agda,
-- asserted-not-identified). Both numbers are printed so the claim can be
-- re-checked with `verify`. Witnesses go to this report only; the four-line
-- state file is unchanged.

describe :: State -> String
describe st = "state " ++ show (completed st) ++ "/" ++ show (totalItems st)
           ++ ", attempts " ++ show (attempts st) ++ ", status " ++ status st

-- Regress: the record claims COMPLETE, the verifier counts more than zero.
regressWitness :: FilePath -> State -> Int -> [String]
regressWitness dir recorded measured =
    [ "WITNESS regress: the recorded state does not identify COMPLETE"
    , "  claim:    COMPLETE (remaining 0)"
    , "  recorded: remaining 0  (" ++ describe recorded ++ ")"
    , "  measured: remaining " ++ show measured ++ "  (engine/verify_register.sh " ++ dir ++ ")"
    , "  Both readings fit the recorded state and disagree on the claim;"
    , "  the measured one is written. Re-check: Engine verify"
    , "  Proof: Fibre.asserted-not-identified, Fibre.regress-refutes"
    , "         (verification/proofs/agda/Fibre.agda)"
    ]

-- | Refuse: no measurement could be taken, so there is no case to derive from.
-- The lines say COMPLETE cannot be derived and, only when the recorded status
-- is COMPLETE, that it is demoted to RUNNING. This function only builds the
-- report; 'updateFromVerifier' writes the demotion.
refuseWitness :: State -> String -> [String]
refuseWitness recorded why =
    [ "WITNESS refuse: no measured case, so COMPLETE cannot be derived"
    , "  claim:    COMPLETE (remaining 0)"
    , "  recorded: " ++ describe recorded
    , "  measured: none (" ++ why ++ ")"
    , "  COMPLETE is derived only from an inhabited measured case."
    ] ++
    [ "  The recorded COMPLETE is demoted to RUNNING: no measurement confirms it."
    | status recorded == statusComplete ] ++
    [ "  A count comes only from measuring the bound target: Engine update"
    , "  Proof: Fibre.complete-needs-case (verification/proofs/agda/Fibre.agda)"
    ]

-- ----------------------------------------------------------- commands ------

die :: String -> IO a
die msg = hPutStrLn stderr ("ERROR: " ++ msg) >> exitWith (ExitFailure 1)

withState :: FilePath -> (State -> IO a) -> IO a
withState root k = readState root >>= either die k

-- Trips the breaker if the incremented count exceeds budget. Returns the
-- state to carry forward, or exits.
bumpOrTrip :: FilePath -> State -> IO State
bumpOrTrip root st0 = do
    let st1 = st0 { attempts = attempts st0 + 1 }
    if attempts st1 > totalItems st1 + attemptSlack
        then do
            writeState root st1 { status = statusStop }
            putStrLn "CIRCUIT BREAKER TRIGGERED: attempt budget exhausted. \
                     \Manual intervention required."
            exitWith (ExitFailure 3)
        else return st1

refuseIfStopped :: State -> IO ()
refuseIfStopped st
    | status st == statusStop =
        die "state is EMERGENCY_STOP. Reset deliberately before continuing."
    | otherwise = return ()

-- A baseline replaces the state, the bound target included: that is the
-- deliberate reset. Re-binding to a different directory is announced, so a
-- switch of target never passes silently; `status` always shows the target.
announceRebind :: FilePath -> FilePath -> IO ()
announceRebind root new = do
    exists <- doesFileExist (stateFileOf root)
    old <- readState root
    case old of
        Right st | target st /= new ->
            hPutStrLn stderr ("NOTE: target re-bound: " ++ target st ++ " -> " ++ new)
        -- An existing state that does not parse may have named another target:
        -- say that it is replaced, so the switch is not silent either.
        Left e | exists ->
            hPutStrLn stderr ("NOTE: replacing a state file that does not parse (" ++ e
                              ++ "); the target is now " ++ new)
        _ -> return ()

-- | Set the baseline explicitly and bind the target that every later update
-- and verify will measure. Refused (exit 1, state untouched) if the target is
-- not an existing directory.
initExplicit :: FilePath -> Int -> FilePath -> IO ()
initExplicit root total dir = bindTarget dir >>= \b -> case b of
    Left e  -> die ("cannot bind a target: " ++ e)
    Right t -> do
        announceRebind root t
        writeState root (State total 0 0 statusRunning t)
        putStrLn $ "Initialised Harvard Engine state with " ++ show total
                 ++ " items; target bound: " ++ t

-- | Set the baseline by measuring the target, and bind it. A failed
-- measurement leaves the state untouched (exit 1).
initMeasured :: FilePath -> FilePath -> IO ()
initMeasured root dir = bindTarget dir >>= \b -> case b of
    Left e  -> die ("cannot bind a target: " ++ e)
    Right t -> runVerifier root t >>= \r -> case r of
        Left e  -> die ("cannot set a baseline without a measurement: " ++ e)
        Right n
            | n > maxTotal -> die ("measured " ++ show n ++ " items, above the bound "
                                   ++ show maxTotal)
            | otherwise -> do
                announceRebind root t
                writeState root (State n 0 0 statusRunning t)
                putStrLn $ "Initialised baseline by MEASURING " ++ t ++ ": "
                         ++ show n ++ " items; target bound."

bumpAttempt :: FilePath -> IO ()
bumpAttempt root = withState root $ \st0 -> do
    refuseIfStopped st0
    st1 <- bumpOrTrip root st0
    writeState root st1
    putStrLn $ "Attempt " ++ show (attempts st1) ++ "/"
             ++ show (totalItems st1 + attemptSlack) ++ " recorded."

-- | The only function that sets the status to COMPLETE, and only from a number
-- this process obtained from the verifier itself. ('bumpAttempt' rewrites a
-- state that is already COMPLETE, but never sets it.)
--
-- An EMERGENCY_STOP state is refused (exit 1). Otherwise the attempt is
-- charged first, which may trip the circuit breaker (exit 3) before the
-- verifier runs. If the verifier gives no count, the attempt stays charged, a
-- recorded COMPLETE is demoted to RUNNING, and the process exits 4. If it
-- gives a count, progress is the total minus that remaining count (at least
-- 0), and the status is COMPLETE exactly when the count is 0.
--
-- It measures only the target bound at the baseline: the caller names no
-- directory here, so it cannot choose what is counted.
updateFromVerifier :: FilePath -> IO ()
updateFromVerifier root = withState root $ \st0 -> do
    refuseIfStopped st0
    st1 <- bumpOrTrip root st0          -- every update costs an attempt
    r <- runVerifier root (target st0)
    case r of
        Left e -> do
            -- The attempt is still counted. A recorded COMPLETE that no
            -- measurement now confirms is demoted: the record alone does not
            -- hold COMPLETE (Fibre.record-does-not-hold-complete).
            let unconfirmed = status st0 == statusComplete
                st2 = if unconfirmed then st1 { status = statusRunning } else st1
            writeState root st2
            hPutStrLn stderr ("VERIFICATION FAILED: " ++ e)
            hPutStrLn stderr $ if unconfirmed
                then "status demoted from COMPLETE to RUNNING. COMPLETE is unreachable without a count."
                else "status unchanged. COMPLETE is unreachable without a count."
            mapM_ (hPutStrLn stderr) (refuseWitness st0 e)
            exitWith (ExitFailure 4)
        Right remaining -> do
            let done = max 0 (totalItems st1 - remaining)
                st2  = st1 { completed = done
                           , status = if remaining == 0 then statusComplete else statusRunning }
            writeState root st2
            putStrLn $ "Verified " ++ target st0
            putStrLn $ "  remaining (measured): " ++ show remaining
            putStrLn $ "  progress: " ++ show done ++ "/" ++ show (totalItems st2)
            putStrLn $ "  status:   " ++ status st2
            when (status st0 == statusComplete && remaining > 0) $
                mapM_ putStrLn (regressWitness (target st0) st0 remaining)

-- | Print the bound target's current count; the state is never written. When
-- no count can be obtained it exits 4, as `update` does.
verifyOnly :: FilePath -> IO ()
verifyOnly root = withState root $ \st -> runVerifier root (target st) >>= \r -> case r of
    Left e  -> hPutStrLn stderr ("VERIFICATION FAILED: " ++ e) >> exitWith (ExitFailure 4)
    Right n -> print n

showStatus :: FilePath -> IO ()
showStatus root = withState root $ \st -> putStrLn $
    status st ++ "  " ++ show (completed st) ++ "/" ++ show (totalItems st)
    ++ " (attempts " ++ show (attempts st) ++ ")  target " ++ target st

usage :: IO a
usage = do
    mapM_ (hPutStrLn stderr)
        [ "Usage: Engine <command>"
        , "  init <total> <targetdir>  set the baseline explicitly; bind the target"
        , "  init-from <targetdir>     set the baseline by MEASURING the target; bind it"
        , "  attempt                   record an attempt (arms the circuit breaker)"
        , "  update                    re-measure the bound target and record progress"
        , "  verify                    print the bound target's count; no state change"
        , "  status                    print current state"
        , ""
        , "`update <remaining>` from the original engine has been REMOVED, and so"
        , "has `update <targetdir>`: the target is bound when the baseline is set."
        , "Progress cannot be asserted by a caller; it is only ever derived from"
        , "engine/verify_register.sh run on the bound target."
        ]
    exitWith (ExitFailure 2)

main :: IO ()
main = do
    args <- getArgs
    findRoot >>= either die (`dispatch` args)
  where
    dispatch root args = case args of
        ["init", n, dir]      -> case natural n of
            Just t | t <= maxTotal -> initExplicit root t dir
            _ -> die ("init expects a natural number up to " ++ show maxTotal
                      ++ ", got " ++ show n)
        ["init-from", dir]    -> initMeasured root dir
        ["attempt"]           -> bumpAttempt root
        ["update"]            -> updateFromVerifier root
        ["verify"]            -> verifyOnly root
        ["status"]            -> showStatus root
        _                     -> usage
