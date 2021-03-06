from plumbum import local
import sys, getopt
import yaml

cp = local['cp']
mv = local['mv']


def makebuilddir(dir, newfrom, name, tag):
    newimg = '%s--%s' % (name, tag)
    newdir = dir + '/build/' + newimg
    ruledir = dir + '/repo/' + name
    cp['-rf', ruledir, newdir]()
    mv[newdir + '/Dockerfile', newdir + '/DockerfileOld']()

    newDockerfile = open(newdir+'/Dockerfile', 'w')
    for line in open(newdir+'/DockerfileOld').readlines():
        if line.strip().startswith('FROM'):
            newDockerfile.write('FROM %s\n' % newfrom)
        else:
            newDockerfile.write(line)
    newDockerfile.close()

def generate(file, dir):
    inputdata = None
    merged = []
    with open(file, 'r') as stream:
        inputdata = yaml.load(stream)
    chains = inputdata['buildchains']
    for chain in chains:
        name = ''
        tag = ''
        for img in reversed(chain):
            if 'rule' in img:
                newfrom = '%s:%s' % (name, tag)
                tag = '%s-%s' % (name, tag)
                name = img['rule']
                newimg = '%s--%s' % (name, tag)
                if not newimg in merged:
                    merged.append(newimg)
                    makebuilddir(dir, newfrom, name, tag)
            else:
                name = img['name']
                tag = img['tag']
    print merged
    buildcmd = lambda name: 'docker build ./%s -t %s\n' % (name, name.replace('--', ':'))
    commands = [buildcmd(m) for m in merged]
    f = open(dir+'/build/build.sh', 'w')
    f.writelines(commands)
    f.close()


def main(argv):
    inputfile = ''
    workingdir = ''
    try:
        opts, args = getopt.getopt(argv,"hi:d:",["ifile=","dir="])
    except getopt.GetoptError:
        print 'dockerfilegen.py -i <inputfile> -d <working dir>'
        sys.exit(2)
    for opt, arg in opts:
        if opt == '-h':
            print 'dockerfilegen.py -i <inputfile> -d <workding dir>'
            sys.exit()
        elif opt in ("-i", "--ifile"):
            inputfile = arg
        elif opt in ("-d", "--dir"):
            workingdir = arg
    print 'Input file is "', inputfile
    print 'Output file is "', workingdir
    if inputfile == '' or workingdir == '':
        print 'input file and working directory required: dockerfilegen.py -i <inputfile> -d <working dir>'

    generate(inputfile, workingdir)



if __name__ == "__main__":
    main(sys.argv[1:])