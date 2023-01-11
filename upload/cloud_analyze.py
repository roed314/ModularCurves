
import os
import re
from collections import defaultdict, Counter
from numpy import mean, median, std
from cloud_common import get_output_data
ope = os.path.exists

def timing_statistics(output_file=None):
    timing_data = [line[1:].strip() for line in get_output_data(output_file=None) if line[0] == "T"]
    by_label = defaultdict(list)
    for line in timing_data:
        label, line = line.split("|")
        by_label[label].append(line)
    start_re = re.compile("Starting (.*)")
    end_re = re.compile("Finished (.*) in (.*)")
    unfinished = {}
    unstarted = {}
    by_task = defaultdict(list)
    uby_task = defaultdict(list)
    for label, lines in by_label.items():
        started = [start_re.fullmatch(x) for x in lines]
        started = [m.group(1) for m in started if m is not None]
        finished = [end_re.fullmatch(x) for x in lines]
        timings = [float(m.group(2)) for m in finished if m is not None]
        finished = [m.group(1) for m in finished if m is not None]
        for task, t in zip(finished, timings):
            # 33 is to truncate the specific j-invariant in "computing rational points above j="
            by_task[task[:33]].append((t, label))
        UF = set(started).difference(set(finished))
        US = set(finished).difference(set(started))
        if UF:
            unfinished[label] = UF
            for task in UF:
                uby_task[task[:33]].append(label)
        if US:
            unstarted[label] = US
    for task, data in by_task.items():
        times = [pair[0] for pair in data]
        level = [int(pair[1].split(".")[0]) for pair in data]
        genus = [int(pair[1].split(".")[2]) for pair in data]
        printtask = task + " "*(33-len(task))
        by_level = defaultdict(list)
        for N, t in zip(level, times):
            by_level[N].append(t)
        by_genus = defaultdict(list)
        for g, t in zip(genus, times):
            by_genus[g].append(t)

        ulevel = [int(label.split(".")[0]) for label in uby_task.get(task, [])]
        uby_level = Counter(ulevel)
        ugenus = [int(label.split(".")[2]) for label in uby_task.get(task, [])]
        uby_genus = Counter(ugenus)
        a = mean(times)
        b = median(times)
        c = std(times)
        d = max(times)
        e = len(times)
        f = len(uby_task.get(task, []))
        print(f"{printtask}       Mean ({a:5.2f}) Median ({b:5.2f}) Std ({c:5.2f}) Max ({d:6.2f}) OK ({e:<3}) Bad ({f})\n")
        for N in sorted(set(list(by_level) + list(uby_level))):
            if N in by_level:
                ts = by_level[N]
                a = mean(ts)
                b = median(ts)
                c = std(ts)
                d = max(ts)
                e = len(ts)
                f = uby_level.get(N, 0)
                print(f"{printtask} N={N:<3} Mean ({a:5.2f}) Median ({b:5.2f}) Std ({c:5.2f}) Max ({d:6.2f}) OK ({e:<3}) Bad ({f})")
            else:
                f = uby_level[N]
                print(f"{printtask} N={N:<3} {' '*61} Bad ({f})")
        print("")
        for g in sorted(set(list(by_genus) + list(uby_genus))):
            if g in by_genus:
                ts = by_genus[g]
                a = mean(ts)
                b = median(ts)
                c = std(ts)
                d = max(ts)
                e = len(ts)
                f = uby_genus.get(g, 0)
                print(f"{printtask} g={g:<3} Mean ({a:5.2f}) Median ({b:5.2f}) Std ({c:5.2f}) Max ({d:6.2f}) OK ({e:<3}) Bad ({f})")
            else:
                f = uby_genus[g]
                print(f"{printtask} g={g:<3} {' '*61} Bad ({f})")
        print("")
    return unfinished, by_task, uby_task

def errors(show=True):
    error_data = [line[1:].strip() for line in get_output_data() if line[0] == "E"]
    broken = set()
    for line in error_data:
        if "error" in line and "Unable to find good primes in PointSearch; perhaps try parameter SkipSingularityCheck" not in line:
            label = line.split("|", 1)[0]
            broken.add(label)
    if show:
        for line in error_data:
            label = line.split("|", 1)[0]
            if label in broken:
                print(line)
    return broken
