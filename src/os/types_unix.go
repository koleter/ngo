// Copyright 2009 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// +build !windows
// +build !plan9

package os

import (
	"syscall"
	"time"
)

// A fileStat is the implementation of FileInfo returned by Stat and Lstat.
type fileStat struct {
	name    string	//文件的basename
	size    int64	//文件的size，属性上的大小
	mode    FileMode	//记录文件权限
	modTime time.Time	//文件的上次修改日期
	sys     syscall.Stat_t
}

func (fs *fileStat) Size() int64        { return fs.size }
func (fs *fileStat) Mode() FileMode     { return fs.mode }
func (fs *fileStat) ModTime() time.Time { return fs.modTime }
func (fs *fileStat) Sys() interface{}   { return &fs.sys }

func sameFile(fs1, fs2 *fileStat) bool {
	return fs1.sys.Dev == fs2.sys.Dev && fs1.sys.Ino == fs2.sys.Ino
}
